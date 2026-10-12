/-
lets look at the rewrite tactics
h : a = b
rw [h] means replace all occurences of a by b
rw [<-h] means replace all of b by a
-/
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by rw [← h]

example (x : Nat) (h1 : x = 5) : x+2 = 7 := by rw [h1]

example (x y z : Nat) (h : x = y) : x+z=y+z:=by rw [h]

example (x : Nat) : 0 + x = x := by rw [Nat.zero_add]
example (x : Nat) : x + 0 = x := by rw [Nat.add_zero]
example (x : Nat) : 0 + x = x := by simp
example (x : Nat) : x + 0 = x := by rfl
/-
example (x : Nat) : 0 + x = x := by rfl
fails, because the argument of the recursive
definition is the first. Thus here use
tactics simp or rw as shown above.
-/

-- check tells you the type
#check Nat.add_zero
#check Nat.zero_add

-- print shows more about the definition itself
#print Nat.zero_add

/-
The keyword 'example' here is like a nameless proof
not used later. Some how for experimenting and
immediate prove someting not used later.
On the other hand, the keyword 'theorem' gives
a name to a proof for later reuse
-/
theorem myZeroAdd (x:Nat) : 0+x=x := by rw [Nat.zero_add]


-- instead theorem foo : 1+1=2 := rfl
-- one could write:
def foo : Prop := 1+1=2
theorem Foo : foo := rfl

theorem hoo : 1<2 := by decide
-- theorem Hoo : hoo := by decide


def τ := (1+Real.sqrt 5)
