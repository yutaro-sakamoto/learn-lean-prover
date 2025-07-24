theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

#print test

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact ⟨hq, hp⟩

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact ⟨hq, hp⟩

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

example (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim h.right
    . intro hq
      apply Or.inl
      apply And.intro
      . exact h.left
      . exact hq
    . intro hr
      apply Or.inr
      exact ⟨h.left, hr⟩
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      exact hpq.left
      exact Or.inl hpq.right
    . intro hpr
      apply And.intro
      . exact hpr.left
      . exact Or.inr hpr.right
