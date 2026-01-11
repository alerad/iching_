import IChing.Hexagram
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Klein Four-Group Action on Hexagrams

The Klein four-group K₄ = {e, c, r, cr} acts on hexagrams, where c = complement
and r = reverse. These operations commute and are self-inverse.

## Main definitions

* `KleinAction` : The four group elements
* `orbit` : The K₄-orbit of a hexagram

## Main results

* `complement_reverse_comm` : comp ∘ rev = rev ∘ comp
* `orbit_size_two_or_four` : All orbits have size 2 or 4
-/

namespace IChing

open Hexagram

inductive KleinAction
  | e | c | r | cr
  deriving DecidableEq, Repr

namespace KleinAction

instance : Fintype KleinAction := ⟨⟨[e, c, r, cr], by decide⟩, by intro x; cases x <;> decide⟩

def apply : KleinAction → Hexagram → Hexagram
  | e => id
  | c => complement
  | r => reverse
  | cr => complementReverse

def mul : KleinAction → KleinAction → KleinAction
  | e, g => g
  | g, e => g
  | c, c => e
  | r, r => e
  | cr, cr => e
  | c, r => cr
  | r, c => cr
  | c, cr => r
  | cr, c => r
  | r, cr => c
  | cr, r => c

def one : KleinAction := e
def inv : KleinAction → KleinAction := id

theorem mul_assoc (a b d : KleinAction) : mul (mul a b) d = mul a (mul b d) := by
  cases a <;> cases b <;> cases d <;> rfl

theorem one_mul (a : KleinAction) : mul one a = a := by cases a <;> rfl
theorem mul_one (a : KleinAction) : mul a one = a := by cases a <;> rfl
theorem inv_mul (a : KleinAction) : mul (inv a) a = one := by cases a <;> rfl

instance : Group KleinAction where
  mul := mul
  mul_assoc := mul_assoc
  one := one
  one_mul := one_mul
  mul_one := mul_one
  inv := inv
  inv_mul_cancel := inv_mul

theorem apply_one (x : Hexagram) : apply 1 x = x := rfl

theorem apply_mul (g h : KleinAction) (x : Hexagram) :
    apply (g * h) x = apply g (apply h x) := by
  cases g <;> cases h
  case e.e => rfl
  case e.c => rfl
  case e.r => rfl
  case e.cr => rfl
  case c.e => rfl
  case r.e => rfl
  case cr.e => rfl
  case c.c =>
    show x = complement (complement x)
    exact (complement_involutive x).symm
  case c.r => rfl
  case c.cr =>
    show reverse x = complement (complementReverse x)
    unfold complementReverse
    exact (complement_involutive (reverse x)).symm
  case r.c =>
    show complementReverse x = reverse (complement x)
    exact (complement_reverse_comm x).symm
  case r.r =>
    show x = reverse (reverse x)
    exact (reverse_involutive x).symm
  case r.cr =>
    show complement x = reverse (complementReverse x)
    unfold complementReverse
    rw [← complement_reverse_comm, reverse_involutive]
  case cr.c =>
    show reverse x = complementReverse (complement x)
    unfold complementReverse
    rw [← complement_reverse_comm, complement_involutive]
  case cr.r =>
    show complement x = complementReverse (reverse x)
    unfold complementReverse
    rw [reverse_involutive]
  case cr.cr =>
    show x = complementReverse (complementReverse x)
    exact (complementReverse_involutive x).symm

instance : MulAction KleinAction Hexagram where
  smul := apply
  one_smul := apply_one
  mul_smul g h x := apply_mul g h x

end KleinAction

namespace Hexagram

def orbit (h : Hexagram) : Finset Hexagram :=
  {h, complement h, reverse h, complementReverse h}

theorem mem_orbit_self (h : Hexagram) : h ∈ orbit h := by
  unfold orbit
  exact Finset.mem_insert_self h _

theorem orbit_closed (h : Hexagram) (g : KleinAction) : g • h ∈ orbit h := by
  cases g
  · exact mem_orbit_self h
  · unfold orbit; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  · unfold orbit; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  · unfold orbit; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

theorem complement_ne_self (h : Hexagram) : complement h ≠ h := by
  intro heq
  have h0 := congrFun heq 0
  unfold complement flipBit at h0
  have hval : (1 : ℕ) - (h 0).val = (h 0).val := congrArg Fin.val h0
  have hlt := (h 0).isLt
  omega

theorem orbit_size_two_or_four (h : Hexagram) :
    (orbit h).card = 2 ∨ (orbit h).card = 4 := by
  have H : ∀ h : Hexagram, (orbit h).card = 2 ∨ (orbit h).card = 4 := by native_decide
  exact H h

end Hexagram

end IChing
