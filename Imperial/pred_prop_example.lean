section
open classical

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r := 
λh, exists.elim h (λ_, id)

example : (∃ x : α, r) → r := 
by { intro h, cases h, assumption }

example : r → (∃ x : α, r) := 
exists.intro a 

include a
example : r → (∃ x : α, r) := 
by { intro, constructor, assumption' }
omit a

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
⟨λh, exists.elim h (λh1, λh2, ⟨⟨h1, h2.left⟩, h2.right⟩),
λh, exists.elim (h.left) (λh1, λh2, ⟨h1, h2, h.right⟩)⟩ 

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
by { constructor; { intro h, cases h with h1 h2, cases h1 <|> cases h2, 
    repeat { constructor }, assumption' } }

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
⟨λh, exists.elim h 
    (λh1, λh2, h2.elim (λh3, or.inl ⟨h1, h3⟩) (λh3, or.inr ⟨h1, h3⟩)),
λh, h.elim 
    (λh1, exists.elim h1 (λh2, λh3, ⟨h2, or.inl h3⟩)) 
    (λh1, exists.elim h1 (λh2, λh3, ⟨h2, or.inr h3⟩))⟩ 

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
by { constructor; intro h, 
    { cases h with _ h1, cases h1,
        { left, constructor, assumption }, 
        { right, constructor, assumption } },
    { cases h with h1 h1; cases h1; 
        constructor, { left, assumption }, { right, assumption } } }

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
⟨λh, λh1, exists.elim h1 (λh2, λh3, h3 (h h2)),
λh, λh1, by_contradiction (λh2, h (exists.intro h1 h2))⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
by { constructor; intros h h1,
    { cases h1 with _ h2, apply h2, apply h },
    { apply by_contradiction, intro, apply h, constructor, assumption} }

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
⟨λh, exists.elim h (λh1, λh2, λh3, (h3 h1) h2),
λh, by_contradiction (λh1, h (λh2, λh3, h1 ⟨h2, h3⟩))⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
by { constructor; intro h,
    { cases h, intro h1, apply h1, assumption },
    { apply by_contradiction, intro h1, apply h,
    repeat { intro }, apply h1, constructor, assumption' } }

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
⟨λh, λh1, show ¬ p h1, from λh2, h (exists.intro h1 h2),
λh, λh1, exists.elim h1 (λh2, λh3, (h h2) h3)⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
by { constructor, 
    { intro h, repeat { intro }, apply h, constructor, assumption' },
    { intros h h1, cases h1, apply h, assumption' } }

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
⟨λh, by_contradiction (λh1, h (λh2, by_contradiction (λh3, h1 ⟨h2, h3⟩))),
λh, exists.elim h (λh1, λh2, λh3, h2 (h3 h1))⟩

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
by { constructor, 
    { intro h, apply by_contradiction, intro h1, apply h, 
        intro, apply by_contradiction, intro, apply h1, 
        constructor, assumption },
    { intros h h1, cases h with _ h2, apply h2, apply h1 } }

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
⟨λh, λh1, exists.elim h1 h, λh, λ_, λh1, h ⟨_, h1⟩⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
by { constructor, 
    { intros h h1, cases h1, apply h, assumption' },
    { intros h _ _, apply h, constructor, assumption' } }

example : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
⟨λh, λh1, exists.elim h (λ_, λh3, h3 (h1 _)), 
λh, by_cases (λh1, ⟨a, λ_, h h1⟩) 
    (λh1, by_contradiction (λh2, h1 (λh3,
        by_contradiction (λh4, h2 ⟨h3, flip absurd h4⟩))))⟩

include a
example : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
by { constructor,
    { intros h h1, cases h with _ h2, apply h2, apply h1 },
    { intro h, apply by_cases, 
        { intro h1, existsi a, intro, apply h h1 },
        { intro h1, apply by_contradiction, intro h2, apply h1, 
            intro, apply by_contradiction, intro, apply h2, 
            constructor, intro, contradiction } } }

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
⟨λh, λh1, exists.elim h (λh2, λh3, ⟨h2, h3 h1⟩), 
λh, by_cases 
    (λh1, exists.elim (h h1) (λh2, λh3, ⟨h2, λh1, h3⟩)) 
    (λh1, ⟨a, (λh2, absurd h2 h1)⟩)⟩

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
by { constructor, 
    { intros h _, cases h with _ h1, constructor, apply h1, assumption },
    { intro h, apply by_cases,
        { intro h1, cases (h h1), constructor, intro, assumption },
        { intro, existsi a, intro, contradiction } } }
omit a
end
--
section
variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
⟨λh, ⟨λh1, (h h1).left, λh1, (h h1).right⟩,
λh, λh1, ⟨(h.left) h1, (h.right) h1⟩⟩

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
by { constructor,
    { intro h, constructor; intro h1; { cases (h h1), assumption } },
    { intros h _, cases h with h1 h2, constructor, apply h1, apply h2 } }

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
λh, λh1, λh2, (h h2) (h1 h2)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
by { intros h h1 _, apply h, apply h1 }

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
λh, λh1, h.elim (λh2, or.inl (h2 h1)) (λh2, or.inr (h2 h1))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
by { intros h _, cases h, { left, apply h }, { right, apply h } } 

end
--
section
open classical

variables (α : Type) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := 
λh, ⟨λh1, h1 h, λh1, (λh, h1)⟩

example : α → ((∀ x : α, r) ↔ r) := 
by { intro h, constructor, { intro h1, apply h1 h }, { intros, assumption } }

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
⟨λh, by_cases (or.inr) 
    (λh1, or.inl (λh2, (h h2).elim id (λh3, absurd h3 h1))),
λh, h.elim (λh1, λh2, or.inl (h1 h2)) (λh1, λh2, or.inr h1)⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
by { constructor, 
    { intro h, apply by_cases,
        { intro, right, assumption },
        { intro, left, intro, cases (h _), assumption, contradiction } },
    { intros h _, cases h, { left, apply h }, { right, assumption } } }

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
⟨λh, λh1, λh2, h h2 h1, λh, λh1, λh2, h h2 h1⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
by { constructor; { intros h h1 h2, apply (h h2 h1) } }

end