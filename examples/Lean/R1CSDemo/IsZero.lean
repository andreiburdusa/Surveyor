import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic

namespace IsZero

def p : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617
axiom p_prime : p.Prime
instance : Fact p.Prime := by rw [fact_iff]; exact p_prime

def Witness : Type := Fin 4 → ZMod p

def spec (w : Witness) : Prop := (w 2 = 0 ∧ w 1 = 1) ∨ (w 2 ≠ 0 ∧ w 1 = 0 ∧ w 2 * w 3 = 1)

def circuit (w : Witness) : Prop :=
    (1 * (w 2)) * (1 * (w 3)) = 1 * (w 0) + 21888242871839275222246405745257275088548364400416034343698204186575808495616 * (w 1) ∧
    (1 * (w 2)) * (1 * (w 1)) = 0

example : ∀ w : Witness, w 0 = 1 → circuit w → spec w := by
    unfold circuit spec
    intros w w0_is_1
    have : (21888242871839275222246405745257275088548364400416034343698204186575808495616 : ZMod p) = -1 := by decide
    rw [this]
    simp only [w0_is_1, one_mul, zero_add, neg_mul]
    intros h
    by_cases w2_is_0 : w 2 = 0
    · simp only [w2_is_0, zero_mul, and_true] at h
      have h := add_eq_of_eq_add_neg h
      rw [zero_add] at h
      left; exact ⟨w2_is_0, h⟩
    · aesop

end IsZero
