namespace hidden

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩

def even (n : ℕ) : Prop := 2 ∣ n

section user_def
def pow : ℕ → ℕ → ℕ-- [¬ (m = 0 ∧ n = 0)] 
| 0 0 := sorry
| _ 0 := 1
| m (nat.succ n) := m * pow m n
end user_def

-- BEGIN
def prime (n : ℕ) : Prop := 
n > 1 ∧ (∀ m : ℕ, 1 < m ∧ m < n → ¬ divides n m)

def infinitely_many_primes : Prop := 
∀ n : ℕ, prime n → ∃ m : ℕ, m > n ∧ prime m

def Fermat_prime (n : ℕ) : Prop := 
∃ m : ℕ, n = pow 2 (pow 2 m) + 1

def infinitely_many_Fermat_primes : Prop := 
∀ n : ℕ, Fermat_prime n → ∃ m : ℕ, m > n ∧ Fermat_prime m

def goldbach_conjecture : Prop := 
∀ n : ℕ, even n ∧ n > 2 → ∃ p1 p2 : ℕ, prime p1 ∧ prime p2 ∧ n = p1 + p2

def Goldbach's_weak_conjecture : Prop :=
∀ n : ℕ, ¬ even n ∧ n > 5 → ∃ p1 p2 p3 : ℕ, prime p1 ∧ prime p2 ∧ prime p3 ∧ n = p1 + p2 + p3

def Fermat's_last_theorem : Prop := 
∀ n : ℕ, n > 2 → ¬ ∃ a b c : ℕ, pow a n + pow b n = pow c n
-- END

end hidden

section
variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y := 
calc log (x * y) 
        = log (exp (log x) * y) : by rw [exp_log_eq hx]
    ... = log (exp (log x) * exp (log y)) : by rw [exp_log_eq hy]
    ... = log (exp (log x + log y)) : by rw [exp_add]
    ... = log x + log y : by rw [log_exp_eq]
    
end

section
example (x : ℤ) : x * 0 = 0 :=
calc x * 0
        = x * (x - x) : by rw [sub_self]
    ... = x * x - x * x : by rw [mul_sub]
    ... = 0 : by rw [sub_self]
end