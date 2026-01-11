/-!
# I Ching King Wen Optimality

Formal verification that the King Wen sequence of the I Ching encodes
the unique K₄-equivariant perfect matching on {0,1}⁶ minimizing total
Hamming distance.

## Main results

* `kingWen_all_equivariant` : All 32 King Wen pairs are K₄-equivariant
* `priorityPartner_involutive` : The reverse-priority rule defines a valid matching
* `reversePriority_unique` : The optimal matching is unique
* `priorityPartner_minimizes_distance` : Reverse-priority minimizes Hamming cost

## References

See `paper.pdf` for the mathematical exposition.
-/

import IChing.Hexagram
import IChing.Symmetry
import IChing.KingWen
import IChing.KingWenOptimality
import IChing.Canonical
