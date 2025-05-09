import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic

namespace Ex1

def p : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617
axiom p_prime : p.Prime
instance : Fact p.Prime := by rw [fact_iff]; exact p_prime

def Witness : Type := Fin 4 → ZMod p

def spec (w : Witness) : Prop := w 1 = w 2 * w 3


def circuit (w : Witness) : Prop :=
    (21888242871839275222246405745257275088548364400416034343698204186575808495616 * (w 2)) * (1 * (w 3)) = 21888242871839275222246405745257275088548364400416034343698204186575808495616 * (w 1)

example : ∀ w : Witness, w 0 = 1 → circuit w → spec w := by
    unfold circuit spec
    have : (21888242871839275222246405745257275088548364400416034343698204186575808495616 : ZMod p) = -1 := by decide
    rw [this]
    intros w _ h
    aesop


end Ex1
