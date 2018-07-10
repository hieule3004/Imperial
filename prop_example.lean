open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
⟨λh, ⟨h.right, h.left⟩, λh, ⟨h.right, h.left⟩⟩

example : p ∨ q ↔ q ∨ p :=
⟨λh, h.elim (λh₁, or.inr h₁) (λh₁, or.inl h₁),
λh, h.elim (λh₁, or.inr h₁) (λh₁, or.inl h₁)⟩ 

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
⟨λh, ⟨h.left.left, ⟨h.left.right, h.right⟩⟩,
λh, ⟨⟨h.left, h.right.left⟩, h.right.right⟩⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
⟨λh, h.elim 
    (λh₁, h₁.elim (or.inl) (λh₂, or.inr (or.inl h₂))) 
    (λh₁, or.inr (or.inr h₁)),
λh, h.elim 
    (λh₁, or.inl (or.inl h₁))
    (λh₁, h₁.elim (λh₂, or.inl (or.inr h₂)) (or.inr))⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
⟨λh, (h.right).elim
    (λh₁, or.inl ⟨h.left, h₁⟩)
    (λh₁, or.inr ⟨h.left, h₁⟩),
λh, h.elim
    (λh₁, ⟨h₁.left, or.inl (h₁.right)⟩)
    (λh₁, ⟨h₁.left, or.inr (h₁.right)⟩)⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
⟨λh, h.elim
    (λh₁, ⟨or.inl h₁, or.inl h₁⟩)
    (λh₁, ⟨or.inr (h₁.left), or.inr (h₁.right)⟩),
λh, (h.left).elim 
    (or.inl)
    (λh₁, (h.right.elim (or.inl) (λh₂, or.inr ⟨h₁, h₂⟩)))⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
⟨λh, λh₁, h (h₁.left) (h₁.right), 
λh, λh₁, λh₂, h ⟨h₁, h₂⟩⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
⟨λh, ⟨λh₁, h (or.inl h₁), λh₁, h (or.inr h₁)⟩, 
λh, λh₁, h₁.elim (h.left) (h.right)⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
⟨λh, ⟨λh₁, h (or.inl h₁), λh₁, h (or.inr h₁)⟩,  
λh, λh₁, h₁.elim (h.left) (h.right)⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
λh, λh₁, h.elim (λh₂, h₂ h₁.left) (λh₂, h₂ h₁.right)

example : ¬(p ∧ ¬p) := 
λh, (h.right) (h.left)

example : p ∧ ¬q → ¬(p → q) :=
λh, λh₁, (h.right) (h₁ (h.left)) 

example : ¬p → (p → q) :=
λh, λh₁, absurd h₁ h 

example : (¬p ∨ q) → (p → q) :=
λh, λh₁, h.elim (absurd h₁ h₂=) id

example : p ∨ false ↔ p := 
⟨λh, h.elim id (false.elim), or.inl⟩

example : p ∧ false ↔ false := 
⟨and.right, false.elim⟩

example : ¬(p ↔ ¬p) := 
λh, by_cases (λh₁, (h.mp h₁) h₁) (λh₁, h₁ (h.mpr h₁))

example : (p → q) → (¬q → ¬p) :=
λh, λh₁, λh₂, h₁ (h h₂)

-- these require classical reasoning
open classical 
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
λh, by_cases 
    (λh₁, (h h₁).elim (λh₂, or.inl (λh₁, h₂)) (λh₂, or.inr (λh₁, h₂))) 
    (λh₁, or.inl (λh₂, absurd h₂ h₁)) 

example : ¬(p ∧ q) → ¬p ∨ ¬q := 
λh, by_cases (λh₁, or.inr (λh₂, h ⟨h₁, h₂⟩)) (or.inl)

example : ¬(p → q) → p ∧ ¬q := 
λh, by_cases
    (λh₁, by_cases (λh₂, absurd (λh₁, h₂) h) (and.intro h₁))
    (λh₁, absurd (λh₂, absurd h₂ h₁) h)
/- em q
λh, by_cases
    (λh₁, absurd (λh₂, h₁) h)
    (λh₁, by_cases (λh₂, ⟨h₂, h₁⟩) (λh₂, absurd (λh₃, absurd h₃ h₂) h))
-/

example : (p → q) → (¬p ∨ q) := 
λh, by_cases (λh₁, or.inr (h h₁)) (or.inl)

example : (¬q → ¬p) → (p → q) := 
λh, λh₁, by_contradiction (λh₂, (h h₂) h₁)

example : p ∨ ¬p := 
em p 
--by_cases (or.inl) (or.inr)

example : (((p → q) → p) → p) :=
λh, by_contradiction (λh₁, h₁ (h (λh₃, absurd h₃ h₁)))