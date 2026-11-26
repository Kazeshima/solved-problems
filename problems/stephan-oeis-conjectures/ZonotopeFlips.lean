import ZonotopeFlips.Total

/-!
# Stephan's Conjecture 69 (OEIS A060621): flips between tilings of `Z(d + 3, d)`

The statement, in the consistent-graph model of the higher Bruhat order `B(d + 3, d)`:

* `ZonoFlips.Consistent S G` — every neighbourhood of the graph `G` on `S ⊂ ℕ` is an initial
  or a final segment of the remaining vertices;
* `ZonoFlips.flipPairs n` — all pairs `(G, e)` with `G` consistent on `{0, …, n-1}`, `e` a
  non-edge, and `G + e` consistent;
* `ZonoFlips.card_flipPairs_eq : 2 * (flipPairs (d + 3)).card = (d ^ 2 + 11 * d + 24) * 2 ^ d`.

Equivalent forms: `ZonoFlips.two_mul_flipCount`, `ZonoFlips.flipCount_eq`
(`n (n + 5) 2 ^ (n - 4)` for `n ≥ 4`), and `ZonoFlips.flipCount_values` (the ten terms listed
in the OEIS).

The proof classifies the flips at a pair `i < j` into four classes (`card_flipSet`), counts
two of them by deleting forced vertices (`card_DD`, `card_DU`), and gets the other two by
complementation (`card_UU`, `card_UD`).
-/
