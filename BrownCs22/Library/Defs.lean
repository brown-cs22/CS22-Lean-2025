import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Order.LocallyFinite
import Mathlib.Data.Nat.Interval

namespace BrownCs22
namespace Nat

def isOdd (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2 * k + 1

def isEven (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2 * k

lemma quotient_remainder {a b c : ℕ} (h : a % b = c) : ∃ q, a = q*b + c := by
  use a/b
  rw [← h, mul_comm, Nat.div_add_mod]


end Nat


lemma Set.inter_union_cancel_left {α : Type} {s t : Set α} :
  (s ∩ t) ∪ s = s := by simp

lemma Set.inter_union_cancel_right {α : Type} {s t : Set α} :
  (s ∩ t) ∪ t = t := by simp

namespace Int

-- def ModEq (n a b : ℤ) : Prop := n ∣ a - b




-- notation:50 a " ≡ " b " [ZMOD " n "]" => Int.ModEq n a b

end Int

def totient (n : ℕ) : ℕ := ((List.range n).filter n.Coprime).length


open BigOperators FinsetInterval

lemma Finset.sum_uIcc_succ (n : ℕ) (f : ℕ → ℕ) :
    ∑ i in [[0, n+1]], f i = ∑ i in [[0, n]], f i + f (n+1) := by
  have hint : [[0, n + 1]] = Finset.range (n + 2)
  { ext x
    simp [Iff.symm Nat.lt_succ] }
  have hint2 : [[0, n]] = Finset.range (n + 1)
  { ext x
    simp [Iff.symm Nat.lt_succ] }
  rw [hint, hint2]
  simp [Finset.sum_range_succ]

end BrownCs22
