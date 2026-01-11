import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi

/-!
# Hexagrams as Binary Vectors

A hexagram is an element of {0,1}⁶, representing a 6-bit binary string.

## Main definitions

* `Hexagram` : The type `Fin 6 → Fin 2` (64 elements)
* `complement` : Bitwise complement (flips all bits)
* `reverse` : Bit reversal (index i ↦ index 5-i)
* `hammingDist` : Hamming distance between hexagrams

## Main results

* `complement_involutive` : comp(comp(h)) = h
* `reverse_involutive` : rev(rev(h)) = h
* `hammingDist_complement` : d(h, comp(h)) = 6
* `palindrome_count` : Exactly 8 hexagrams satisfy h = rev(h)
-/

namespace IChing

abbrev Hexagram := Fin 6 → Fin 2

namespace Hexagram

theorem card : Fintype.card Hexagram = 64 := by decide

def ofNat (n : ℕ) : Hexagram := fun i => ⟨(n / 2^i.val) % 2, Nat.mod_lt _ (by omega)⟩

def flipBit (b : Fin 2) : Fin 2 := ⟨1 - b.val, by have := b.isLt; omega⟩

theorem flipBit_flipBit (b : Fin 2) : flipBit (flipBit b) = b := by
  simp only [flipBit]
  ext
  simp only [Fin.val_mk]
  have := b.isLt
  omega

def complement (h : Hexagram) : Hexagram := fun i => flipBit (h i)

def reverse (h : Hexagram) : Hexagram := fun i =>
  h ⟨5 - i.val, by have := i.isLt; omega⟩

theorem complement_involutive : Function.Involutive complement := by
  intro h
  funext i
  simp only [complement]
  exact flipBit_flipBit (h i)

theorem reverse_involutive : Function.Involutive reverse := by
  intro h
  funext i
  simp only [reverse]
  congr 1
  ext
  simp only [Fin.val_mk]
  have := i.isLt
  omega

theorem complement_reverse_comm (h : Hexagram) :
    complement (reverse h) = reverse (complement h) := rfl

def complementReverse (h : Hexagram) : Hexagram := complement (reverse h)

theorem complementReverse_involutive : Function.Involutive complementReverse := by
  intro h
  simp only [complementReverse, ← complement_reverse_comm]
  rw [complement_involutive]
  exact reverse_involutive h

def hammingDist (h₁ h₂ : Hexagram) : ℕ :=
  ((Finset.univ : Finset (Fin 6)).filter (fun i => h₁ i ≠ h₂ i)).card

theorem hammingDist_comm (h₁ h₂ : Hexagram) : hammingDist h₁ h₂ = hammingDist h₂ h₁ := by
  simp only [hammingDist]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm

theorem hammingDist_self (h : Hexagram) : hammingDist h h = 0 := by
  simp only [hammingDist, ne_eq, not_true_eq_false, Finset.filter_False, Finset.card_empty]

theorem flipBit_ne (b : Fin 2) : flipBit b ≠ b := by
  simp only [flipBit, ne_eq]
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_mk] at hval
  have := b.isLt
  omega

theorem hammingDist_complement (h : Hexagram) : hammingDist h (complement h) = 6 := by
  simp only [hammingDist, ne_eq, complement]
  have heq : (Finset.univ : Finset (Fin 6)).filter (fun i => h i ≠ flipBit (h i)) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    constructor
    · intro _; trivial
    · intro _; exact (flipBit_ne (h i)).symm
  rw [heq, Finset.card_univ, Fintype.card_fin]

def isPalindrome (h : Hexagram) : Prop := h = reverse h

instance : DecidablePred isPalindrome := fun h => by
  unfold isPalindrome
  infer_instance

theorem palindrome_count : ((Finset.univ : Finset Hexagram).filter isPalindrome).card = 8 := by
  native_decide

end Hexagram

end IChing
