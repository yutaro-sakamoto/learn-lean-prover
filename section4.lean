example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r                -- ∀ (x y z : α), r x y → r y z → r x z
/- (r : α → α → Prop) と 「r x y → r y z → r x z」により x,y,z の型が推論されている -/
#check trans_r a b c          -- r a b → r b c → r a c
#check trans_r a b c hab      -- r b c → r a c
#check trans_r a b c hab hbc  -- r a c
