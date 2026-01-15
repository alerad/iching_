import IChing.KingWen

/-! # King Wen Canonicity -/

namespace IChing

open Hexagram

def isEquivariantMatching (pair : Hexagram → Hexagram) : Prop :=
  ∀ h, pair h ∈ orbit h

theorem kingWen_respects_orbits : ∀ k : Fin 32,
    (kingWenPair k).2 ∈ orbit (kingWenPair k).1 := by
  intro k
  have h := kingWen_all_equivariant k
  unfold isEquivariantPair isOppositePair isReversePair at h
  unfold orbit
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases h with heq | heq
  · right; left; exact heq
  · right; right; left; exact heq

end IChing
