import IChing.Symmetry
import Mathlib.Data.Fin.VecNotation

/-!
# The King Wen Sequence

The King Wen sequence orders the 64 hexagrams into 32 pairs.
This encoding follows the traditional I Ching ordering.

## Main definitions

* `kingWenBinary` : The 64 hexagrams as integers
* `kingWenPair` : The k-th consecutive pair

## Main results

* `kingWen_all_equivariant` : All pairs satisfy h₂ = comp(h₁) or h₂ = rev(h₁)
-/

namespace IChing

open Hexagram

def kingWenBinary : Fin 64 → ℕ := ![
  63, 0, 17, 34, 23, 58, 2, 16, 55, 59, 7, 56, 61, 47, 4, 8,
  25, 38, 3, 48, 41, 37, 32, 1, 57, 39, 33, 30, 18, 45, 28, 14,
  60, 15, 40, 5, 53, 43, 20, 10, 35, 49, 31, 62, 24, 6, 26, 22,
  29, 46, 9, 36, 52, 11, 13, 44, 54, 27, 50, 19, 51, 12, 21, 42
]

def kingWenHex (i : Fin 64) : Hexagram := ofNat (kingWenBinary i)

def kingWenPair (k : Fin 32) : Hexagram × Hexagram :=
  (kingWenHex ⟨2 * k.val, by omega⟩, kingWenHex ⟨2 * k.val + 1, by omega⟩)

def isOppositePair (p : Hexagram × Hexagram) : Prop := p.2 = complement p.1

def isReversePair (p : Hexagram × Hexagram) : Prop := p.2 = reverse p.1

def isEquivariantPair (p : Hexagram × Hexagram) : Prop :=
  isOppositePair p ∨ isReversePair p

instance (p : Hexagram × Hexagram) : Decidable (isOppositePair p) := by
  unfold isOppositePair; infer_instance

instance (p : Hexagram × Hexagram) : Decidable (isReversePair p) := by
  unfold isReversePair; infer_instance

instance (p : Hexagram × Hexagram) : Decidable (isEquivariantPair p) := by
  unfold isEquivariantPair; infer_instance

theorem kingWen_all_equivariant : ∀ k : Fin 32, isEquivariantPair (kingWenPair k) := by decide

end IChing
