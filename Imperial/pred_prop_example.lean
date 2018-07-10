section
open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r := 
λh, exists.elim h (λh1, id)

example : r → (∃ x : α, r) := 
exists.intro a 

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
⟨λh, exists.elim h (λh1, λh2, ⟨⟨h1, h2.left⟩, h2.right⟩),
λh, exists.elim (h.left) (λh1, λh2, ⟨h1, h2, h.right⟩)⟩ 

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
⟨λh, exists.elim h 
    (λh1, λh2, h2.elim (λh3, or.inl ⟨h1, h3⟩) (λh3, or.inr ⟨h1, h3⟩)),
λh, h.elim 
    (λh1, exists.elim h1 (λh2, λh3, ⟨h2, or.inl h3⟩)) 
    (λh1, exists.elim h1 (λh2, λh3, ⟨h2, or.inr h3⟩))⟩ 

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
⟨λh, λh1, exists.elim h1 (λh2, λh3, h3 (h h2)),
λh, λh1, by_contradiction (λh2, h (exists.intro h1 h2))⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
⟨λh, exists.elim h (λh1, λh2, λh3, (h3 h1) h2),
λh, by_contradiction (λh1, h (λh2, show ¬p h2, from λh3, h1 ⟨h2, h3⟩))⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
⟨λh, λh1, show ¬ p h1, from λh2, h (exists.intro h1 h2),
λh, λh1, exists.elim h1 (λh2, λh3, (h h2) h3)⟩

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
⟨λh, by_contradiction (λh1, h (λh2, by_contradiction (λh3, h1 ⟨h2, h3⟩))),
λh, exists.elim h (λh1, λh2, λh3, h2 (h3 h1))⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
⟨λh, λh1, exists.elim h1 h, λh, λh1, λh2, h ⟨h1, h2⟩⟩

example : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
⟨λh, λh1, exists.elim h (λh2, λh3, h3 (h1 h2)), 
λh, by_cases (λh1, ⟨a, (λh3, h h1)⟩) 
    (λh1, by_contradiction (λh2, h1 (λh3, 
        by_contradiction (λh4, h2 ⟨h3, λh5, absurd h5 h4⟩))))⟩

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
⟨λh, λh1, exists.elim h (λh2, λh3, ⟨h2, h3 h1⟩), 
λh, by_cases 
    (λh1, exists.elim (h h1) (λh2, λh3, ⟨h2, λh1, h3⟩)) 
    (λh1, ⟨a, (λh2, absurd h2 h1)⟩)⟩
end
--
section
variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
⟨λh, ⟨λh1, (h h1).left, λh1, (h h1).right⟩,
λh, λh1, ⟨(h.left) h1, (h.right) h1⟩⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
λh, λh1, λh2, (h h2) (h1 h2)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
λh, λh1, h.elim (λh2, or.inl (h2 h1)) (λh2, or.inr (h2 h1))
end
--
section
open classical

variables (α : Type) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := 
λh, ⟨λh1, h1 h, λh1, (λh, h1)⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
⟨λh, by_cases (or.inr) 
    (λh1, or.inl (λh2, (h h2).elim id (λh3, absurd h3 h1))),
λh, h.elim (λh1, λh2, or.inl (h1 h2)) (λh1, λh2, or.inr h1)⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
⟨λh, λh1, λh2, (h h2) h1,
λh, λh1, by_cases (λh2, λh2, (h h2) h1) (λh2, λh3, absurd h3 h2)⟩
end