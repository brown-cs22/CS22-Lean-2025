import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs
import Mathlib.Tactic.Polyrith
import AutograderLib

open Dvd

/-

# Welcome to the Lean section of HW5!

Today we'll explore *induction* in Lean.

The tactics we introduced in class (in Lecture 15) were
`basic_induction`, `induction_from_starting_point`, and `strong_induction`.
Each of these applied when the goal had the shape `∀ n : ℕ, ...`,
which matches our normal induction pattern: it's a technique for proving facts
about all natural numbers (or perhaps all natural numbers starting from some bound).

Take a look at the descriptions of these tactics in the CS22 Lean docs
before you start on these problems!

-/


/-

## Problem 1

Here we prove a fact about divisibility. Which induction principle do you need to use?
Remember that you can `dsimp dvd` to unfold the definition of divisibility.

You may find it convenient to do a *calculation* at some point in your proof.
Here's a reminder of what a calc block looks like
-/

example (a b : ℚ) :
    3*a ^ 2 = b + 5 → (4*a + 1) * (a + 4) = b + a^2 + 17*a + 9 := by
  assume hab
  calc
    (4*a + 1) * (a + 4) = 4*a^2 + a + 16*a + 4 := by ring
    _ = 3*a^2 + a^2 + 17*a + 4 := by ring
    _ = (b + 5) + a^2 + 17*a + 4 := by linarith  -- (*)
    _ = b + a^2 + 17*a + 9 := by ring

/-

Each line of the `calc` block establishes a relation between the right-hand expression
on the previous line, and the expression on the current line.
For example: at the line marked (*) above, we are proving that
`3*a^2 + a^2 + 17*a + 4 = (b + 5) + a^2 + 17*a + 4`.
Each line (other than the first) must begin with an underscore.
Each line must end with `:= by`, followed by a tactic that will prove that line.

We use the tactic `ring` to prove equalities about polynomial expressions,
and `linarith` to substitute equality hypotheses like `hab` into the goal.

In the example above, before we begin the `calc` block, our goal is
`(4*a + 1) * (a + 4) = b + a^2 + 17*a + 9`.
This is why the first expression (on the left hand side of the first line)
is `(4*a + 1) * (a + 4)`,
and the last expression (on the right hand side of the final line)
is` b + a^2 + 17*a + 9`.
-/


@[autograded 4]
theorem problem_1 : ∀ n : ℕ, 3 ∣ n^3 + 2*n := by
  sorry
  done


/-

## Problem 2

No calculation this time, just some logic!
Now we'll prove that every number is either even or odd, phrased in terms of
"divisibility by 2."

-/

@[autograded 4]
theorem problem_2 : ∀ n : ℕ, 2 ∣ n ∨ 2 ∣ n + 1 := by
  sorry
  done
