open List

#eval 1+5
#eval (1+2)*3

#eval String.append "anc" "_"


def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else
    n

#eval maximum 5 6
#check maximum (5 + 8) (2 * 7)
#check maximum
#check 3.14

def primesUnder10 : List Nat := [2, 3, 5, 7]

#eval length primesUnder10

example : y = x → y = z → x = z :=
fun h1 h2 ↦   Eq.trans (Eq.symm h1) h2


-- countdown takes a Nat and returns a list of unexecuted IO actions, one for each Nat:
def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

-- The function runActions takes a list of actions and constructs a single action that runs them all in order:
def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions

#eval runActions (countdown 3)

def xs:List Int := [1, 20]

#check List.filter

#eval List.head? ([] : List Nat)


theorem filter_length_le (xs : List Nat) (pred : Nat → Bool) :
    (xs.filter pred).length ≤ xs.length := by
  exact List.length_filter_le pred xs

-- qsort isn't an easy recursive function in Lean.
-- it seems the problem lean sees, is that the argument of the
-- recursive call does not get smaller. so length (x:xs) < length xs
-- has to be proven first to satisfy lean.
/-
def qsort1 : List Nat → List Nat
  | [] => []
  | p :: xs =>
      qsort1 (xs.filter (fun x => x ≤ p))
      ++ [p]
      ++ qsort1 (xs.filter (fun x => x > p))
termination_by xs => xs.length
-/


-- lists
def ns : List Int := [1,2,3]

def two := ns[1]
