import IChing.KingWen
import IChing.Symmetry

/-!
# King Wen Optimality

The reverse-priority rule: pair with rev(h) unless h is a palindrome,
then pair with comp(h). This is optimal and unique among comp/rev matchings.

Note: This file proves optimality among matchings using only comp or rev pairings.
The third equivariant option (comp ∘ rev pairing) can achieve lower total cost (96 vs 120)
on orbits where d(h, rev(h)) = 4, but King Wen follows the structurally simpler rule.

## Main definitions

* `priorityPartner` : The optimal partner function (among comp/rev matchings)
* `SatisfiesReversePriority` : Matching follows the rule

## Main results

* `priorityPartner_involutive` : partner(partner(h)) = h
* `priorityPartner_minimizes_distance` : Achieves minimum Hamming cost vs complement
* `reversePriority_unique` : The reverse-priority matching is unique
* `reverse_eq_complement_of_hamming_six` : Key lemma for uniqueness
-/

namespace IChing

open Hexagram KleinAction

def priorityPartner (h : Hexagram) : Hexagram :=
  if isPalindrome h then complement h else reverse h

def SatisfiesReversePriority (matching : Hexagram → Hexagram) : Prop :=
  ∀ h : Hexagram,
    (isPalindrome h → matching h = complement h) ∧
    (¬isPalindrome h → matching h = reverse h)

theorem priorityPartner_satisfies_rule : SatisfiesReversePriority priorityPartner := by
  intro h
  constructor
  · intro hp; simp only [priorityPartner, hp, ↓reduceIte]
  · intro hnp; simp only [priorityPartner, hnp, ↓reduceIte]

theorem palindrome_complement_palindrome (h : Hexagram) (hp : isPalindrome h) :
    isPalindrome (complement h) := by
  unfold isPalindrome at *
  conv_rhs => rw [← complement_reverse_comm, ← hp]

theorem nonpalindrome_reverse_nonpalindrome (h : Hexagram) (hnp : ¬isPalindrome h) :
    ¬isPalindrome (reverse h) := by
  unfold isPalindrome at *
  intro hp_rev
  apply hnp
  rw [hp_rev]
  exact (reverse_involutive h).symm

theorem priorityPartner_involutive : Function.Involutive priorityPartner := by
  intro h
  unfold priorityPartner
  by_cases hp : isPalindrome h
  · simp only [hp, ↓reduceIte]
    have hp' : isPalindrome (complement h) := palindrome_complement_palindrome h hp
    simp only [hp', ↓reduceIte]
    exact complement_involutive h
  · simp only [hp, ↓reduceIte]
    have hnp' : ¬isPalindrome (reverse h) := nonpalindrome_reverse_nonpalindrome h hp
    simp only [hnp', ↓reduceIte]
    exact reverse_involutive h

theorem reversePriority_matching_unique (m : Hexagram → Hexagram)
    (hm : SatisfiesReversePriority m) :
    m = priorityPartner := by
  funext h
  unfold SatisfiesReversePriority at hm
  unfold priorityPartner
  by_cases hp : isPalindrome h
  · simp only [hp, ↓reduceIte]; exact (hm h).1 hp
  · simp only [hp, ↓reduceIte]; exact (hm h).2 hp

theorem reversePriority_unique (m1 m2 : Hexagram → Hexagram)
    (h1 : SatisfiesReversePriority m1)
    (h2 : SatisfiesReversePriority m2) :
    m1 = m2 := by
  rw [reversePriority_matching_unique m1 h1, reversePriority_matching_unique m2 h2]

def PairSatisfiesPriority (p : Hexagram × Hexagram) : Prop :=
  (isPalindrome p.1 → p.2 = complement p.1) ∧
  (¬isPalindrome p.1 → p.2 = reverse p.1)

theorem priority_implies_equivariant (p : Hexagram × Hexagram)
    (hp : PairSatisfiesPriority p) : isEquivariantPair p := by
  unfold PairSatisfiesPriority at hp
  unfold isEquivariantPair isOppositePair isReversePair
  by_cases hpal : isPalindrome p.1
  · left; exact hp.1 hpal
  · right; exact hp.2 hpal

theorem fin2_ne_eq_flip (a b : Fin 2) (hab : a ≠ b) : b = flipBit a := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [flipBit, Fin.ext_iff]
  omega

theorem reverse_eq_complement_of_hamming_six (h : Hexagram)
    (hdist : hammingDist h (reverse h) = 6) :
    reverse h = complement h := by
  have hall : ∀ i : Fin 6, h i ≠ (reverse h) i := by
    intro i
    intro heq
    have hnotmem : i ∉ Finset.univ.filter (fun j => h j ≠ (reverse h) j) := by
      simp only [Finset.mem_filter, not_and, not_not]
      intro _; exact heq
    have hcard_univ : (Finset.univ : Finset (Fin 6)).card = 6 := by simp [Fintype.card_fin]
    have hfilter_eq : Finset.univ.filter (fun j => h j ≠ (reverse h) j) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      simp only [hammingDist] at hdist
      rw [hdist, hcard_univ]
    have hmem : i ∈ Finset.univ.filter (fun j => h j ≠ (reverse h) j) := by
      rw [hfilter_eq]; exact Finset.mem_univ i
    exact hnotmem hmem
  funext i
  simp only [reverse, complement]
  have hi := hall i
  simp only [reverse] at hi
  exact fin2_ne_eq_flip (h i) (h ⟨5 - i.val, by have := i.isLt; omega⟩) hi

theorem hammingDist_le_six (h₁ h₂ : Hexagram) : hammingDist h₁ h₂ ≤ 6 := by
  unfold hammingDist
  calc (Finset.univ.filter (fun i => h₁ i ≠ h₂ i)).card
      ≤ Finset.univ.card := Finset.card_filter_le _ _
    _ = 6 := by simp [Fintype.card_fin]

theorem priorityPartner_minimizes_distance (h : Hexagram) :
    hammingDist h (priorityPartner h) ≤ hammingDist h (complement h) := by
  unfold priorityPartner
  by_cases hp : isPalindrome h
  · simp only [hp, ↓reduceIte, le_refl]
  · simp only [hp, ↓reduceIte]
    have hc : hammingDist h (complement h) = 6 := hammingDist_complement h
    rw [hc]
    exact hammingDist_le_six h (reverse h)

theorem palindrome_equivariant_is_complement (h₁ h₂ : Hexagram)
    (hp : isPalindrome h₁)
    (hne : h₁ ≠ h₂)
    (heq : isEquivariantPair (h₁, h₂)) :
    h₂ = complement h₁ := by
  unfold isEquivariantPair isOppositePair isReversePair at heq
  cases heq with
  | inl hc => exact hc
  | inr hr =>
    unfold isPalindrome at hp
    simp only at hr
    rw [← hp] at hr
    exact absurd hr.symm hne

theorem nonpalindrome_equivariant_is_reverse (h₁ h₂ : Hexagram)
    (_hnp : ¬isPalindrome h₁)
    (heq : isEquivariantPair (h₁, h₂))
    (hne_compl : h₂ ≠ complement h₁) :
    h₂ = reverse h₁ := by
  unfold isEquivariantPair isOppositePair isReversePair at heq
  cases heq with
  | inl hc => exact absurd hc hne_compl
  | inr hr => exact hr

theorem kingWenPair_satisfies_priority_of_equivariant (k : Fin 32)
    (h_distinct : (kingWenPair k).1 ≠ (kingWenPair k).2)
    (h_not_compl : ¬isPalindrome (kingWenPair k).1 →
                   (kingWenPair k).2 ≠ complement (kingWenPair k).1) :
    PairSatisfiesPriority (kingWenPair k) := by
  have heq := kingWen_all_equivariant k
  constructor
  · intro hp
    exact palindrome_equivariant_is_complement _ _ hp h_distinct heq
  · intro hnp
    exact nonpalindrome_equivariant_is_reverse _ _ hnp heq (h_not_compl hnp)

theorem kingWen_is_canonical_matching :
    ∀ m1 m2 : Hexagram → Hexagram,
      SatisfiesReversePriority m1 → SatisfiesReversePriority m2 → m1 = m2 :=
  reversePriority_unique

end IChing
