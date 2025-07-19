--import data.int.basic
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

variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

#check Eq.refl
#check Eq.symm
#check Eq.trans

universe u

#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}

namespace foo
  variable (α : Type) (a b c d : α)
  variable (hab : a = b) (hcb : c = b) (hcd : c = d)
  example : a = d :=
    Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
end foo

namespace foo1
  variable (α β : Type)
  example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
  example (a : α) (b: β) : (a, b).1 = a := Eq.refl _
  example : 2 + 3 = 5 := Eq.refl _

  example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
  example (a : α) (b: β) : (a, b).1 = a := rfl
  example : 2 + 3 = 5 := rfl

  example (α : Type) (a b : α) (p : α → Prop)
          (h1 : a = b) (h2 : p a) : p b := Eq.subst h1 h2

  example (α : Type) (a b : α) (p : α → Prop)  -- h2の型の中に登場するh1の左辺をh1の右辺で書き換える
          (h1 : a = b) (h2 : p a) : p b :=
          h1 ▸ h2
  example (α : Type) (a b : α) (p : α → Prop)
          (h1 : a = b) (h2 : p b) : p a :=
          h1 ▸ h2
end foo1

namespace congrExample
  variable (α : Type)
  variable (a b : α)
  variable (f g : α → Nat)
  variable (h₁ : a = b)
  variable (h₂ : f = g)

  example : f a = f b := congrArg f h₁
  example : f a = g a := congrFun h₂ a
  example : f a = g b := congr h₂ h₁
end congrExample

namespace SimpleIdentity
  variable (a b c : Nat)

  example : a + 0 = a := Nat.add_zero a
  example : 0 + a = a := Nat.zero_add a
  example : a * 1 = a := Nat.mul_one a
  example : 1 * a = a := Nat.one_mul a
  example : a + b = b + a := Nat.add_comm a b
  example : a + b + c = a + (b + c) := Nat.add_assoc a b c
  example : a * b = b  * a := Nat.mul_comm a b
  example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
  example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
  example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
  example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
end SimpleIdentity

namespace Integers
variable (x y z : ℤ)
example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
    Nat.mul_add (x + y) x y
  have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
    (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
  h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
end Integers

#check Eq.subst

namespace Equations
variable (a b c d e : Nat)

theorem T
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4

theorem T1
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

theorem T2
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
  calc
    a = d + 1 := by rw [h1, h2, h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e := by rw [h4]

theorem T3
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
    by rw [h1, h2, h3, Nat.add_comm, h4]

theorem T4
    (h1 : a = b)
    (h2 : b = c + 1)
    (h3 : c = d)
    (h4 : e = 1 + d) :
    a = e :=
    by simp [h1, h2, h3, Nat.add_comm, h4]

example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
  calc
    a = b := h1
    _ < b + 1 := Nat.lt_succ_self b
    _ ≤ c + 1 := Nat.succ_le_succ h2
    _ < d := h3

def divides (x y : Nat) : Prop :=
  ∃ k, k * x  = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance: Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
  calc
    divides x y := h₁
    _ = z := h₂
    divides _ (2 * z) := divides_mul ..

infix:50 " | " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
  calc
    x | y := h₁
    _ = z := h₂
    _ | 2  * z := divides_mul ..

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y := by rw [←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y)
    _ = (x + y) * x + (x + y) * y := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y := by rw [←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  by simp [Nat.mul_add, Nat.add_mul, ←Nat.add_assoc]

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro

variable (g : Nat → Nat → Nat)

theorem gex1
  (hg : g 0 0 = 0)
  : ∃ x, g x x = x
  := ⟨0, hg⟩

theorem gex2
  (hg : g 0 0 = 0)
  : ∃ x, g x 0 = x
  := ⟨0, hg⟩

theorem gex3
  (hg : g 0 0 = 0)
  : ∃ x, g 0 0 = x
  := ⟨0, hg⟩

theorem gex4
  (hg : g 0 0 = 0)
  : ∃ x, g x x = 0
  := ⟨0, hg⟩

set_option pp.explicit true
#print gex1
#print gex2
#print gex3
#print gex4

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x , q x ∧ p x :=
  Exists.elim h
    (fun w =>
      fun hw : p w ∧ q w =>
        show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

#check @Exists.elim
end Equations

section exist_prop
variable (a : α) (p : α → Prop) (h : p a)
#check Exists.intro a h
end exist_prop

section sigma_type
variable (a : α) (p : α → Type) (h : p a)
#check Sigma.mk a h

variable (a : α) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hpw : p w), (hqw : q w)⟩ => ⟨w, hqw, hpw⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def is_even(a : Nat) : Prop := ∃ b : Nat, a = 2 * b

example {a b : Nat} (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))

example : ∀ a b : Nat, is_even a → is_even b → is_even (a + b) :=
  fun a : Nat =>
  fun b : Nat =>
  fun ⟨(w1 : Nat), (hw1 : a = 2 * w1)⟩ =>
  fun ⟨(w2 : Nat), (hw2 : b = 2 * w2)⟩ =>
    have hw3 : a + b = 2 * (w1 + w2) :=
      calc a + b
        _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
        _ = 2 * (w1 + w2) := by rw [Nat.mul_add]
    ⟨(w1 + w2 : Nat), (hw3 : a + b = 2 * (w1 + w2))⟩

example {a b : Nat}(h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
end sigma_type

section excercise

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := fun t =>
  match t with
  | ⟨s, u⟩ => u

example (a : α) : r → (∃ x : α, r) := fun s : r => ⟨(a : α), (s : r)⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun h : ∃ x, p x ∧ r =>
      match h with
      | ⟨ix, ⟨pix, ir⟩⟩ => ⟨⟨ix, pix⟩, ir⟩)
    (fun h : (∃ x, p x) ∧ r =>
      match h with
      | ⟨⟨ix, pix⟩, ir⟩ => ⟨ix, ⟨pix, ir⟩⟩)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  ⟨(fun ⟨(ix : α), (pix : p ix), (ir : r)⟩ => ⟨⟨ix, pix⟩, ir⟩),
   (fun ⟨⟨(ix : α), (pix : p ix)⟩, (ir : r)⟩ => ⟨ix, pix, ir⟩)⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  ⟨fun (⟨ix, pxqx⟩ : ∃ x, p x ∨ q x) =>
    Or.elim pxqx
      (fun (pix : p ix) => Or.inl ⟨ix, pix⟩)
      (fun (qix : q ix) => Or.inr ⟨ix, qix⟩),
  fun (h : (∃ x, p x) ∨ (∃ x, q x)) =>
    Or.elim h
    (fun ⟨ix, pix⟩ => ⟨ix, Or.inl pix⟩)
     fun ⟨ix, qix⟩ => ⟨ix, Or.inr qix⟩⟩

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  ⟨
    fun h : (∀ x , p x) =>
      fun  (⟨ix, npix⟩ : (∃ x, ¬ p x)) =>
        show False from npix (h ix),
    --fun (h : ¬ (∃ x, ¬ p x)) =>
      --fun ix => Or.elim (Classical.em (p ix))
      --  (fun (hpix : p ix) => hpix)
      --  (fun (hnpix : ¬ p ix) => False.elim (h ⟨ix, hnpix⟩))
    fun (h : ¬ (∃ x, ¬ p x)) =>
      fun ix =>
        Classical.byContradiction (fun (hnpix : ¬ p ix) => h ⟨ix, hnpix⟩)
  ⟩
end excercise
