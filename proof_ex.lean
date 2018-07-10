open classical

variables (men : Type) (barber : men)
variable  (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false := 
let h0 := (h barber) in by_cases (λh1, (h0.mp h1) h1) (λh1, h1 (h0.mpr h1))