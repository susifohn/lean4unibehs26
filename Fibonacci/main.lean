import Mathlib

set_option linter.style.longLine false

def fib : Nat -> Nat
    | 0 => 0
    | 1 => 1
    | n+2 => fib n + fib (n+1)

def fib2 (n : Nat) : Nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | k+2 => fib2 k + fib2 (k+1)

noncomputable def goldenRatio : Real := (1 + Real.sqrt 5) / 2
noncomputable def goldenRatioConj : Real := (1 - Real.sqrt 5) / 2

theorem fib_non_negative (n : Nat) : fib n >= 0 := by
    induction n using Nat.strong_induction_on with
    -- ∀n.P(n)
    -- normal induction:
    ---- P(0)
    ---- P(n) -> P(n+1), for arbitrary n
    -- strong induction: [∀m < n . P(m)] -> P(n)
    | h n ih =>
        -- h: name required by the tactic for the inductive case
        -- ih = ‘∀m < n . fib m >= 0’
        match n with
        | 0 => simp [fib]   -- Lean evaluates fib 0 to 0 and sees that 0 >= 0
        -- goal: fib 0 >= 0
        -- subgoal after simp: 0 >= 0
        | 1 => simp [fib]   -- idem
        | n+2 =>
            -- goal: fib (n+2) >= 0
            rw [fib]    -- rewrites ‘fib (n+2)’ as ‘fib n + fib (n+1)’
            -- goal: fib n + fib (n+1) >= 0
            -- have ih1 : n < n+2 -> fib n >= 0 := ih n
            have ih1 : fib n >= 0 := ih n (by omega)
            -- ‘(by omega)’ is an inline tactic block to automatically prove simple facts on the fly
            -- Lean expects a proof term; ‘by’ switches into tactic mode
            -- ‘omega’ is a tactic for Presburger arithmetic
            have ih2 : fib (n+1) >= 0 := ih (n+1) (by omega)
            -- At this point we have:
            -- ih1 : fib n >= 0
            -- ih2 : fib (n+1) >= 0
            -- |- fib n + fib (n+1) >= 0
            omega


theorem Binet_fmla (n : Nat) : (fib n : Real) = (goldenRatio^n - goldenRatioConj^n) / (Real.sqrt 5) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        -- ih = ‘∀m < n . ↑(fib m) = (goldenRatio^m - goldenRatioConj^m) / (Real.sqrt 5)’
        match n with
        | 0 =>
            -- goal: ‘(fib 0 : Real) = (goldenRatio^0 - goldenRatioConj^0) / (Real.sqrt 5)’
            rw [fib]
            -- goal: ‘(0 : Real) = (goldenRatio^0 - goldenRatioConj^0) / (Real.sqrt 5)’
            sorry
        | 1 => sorry
        | n+2 => sorry

