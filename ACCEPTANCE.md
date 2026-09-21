# ACCEPTANCE — JSP-000361 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000361
- Awards CONTRIBUTING: https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md

## Exact original question (English)

> For a fixed infinite integer set, how many divisors of a single integer can belong to that set?

The accepted resolution: Let A⊆ℕ be infinite and d_A(n) = #{a∈A : a|n}. Erdős–Sárközy (ErSa80) proved that for every k, limsup_{x→∞} max_{n<x} d_A(n) / (∑_{a∈A∩[1,x)} 1/a)^k = ∞.

## Required Lean theorem name(s) (FULL statement)

| Lean name | Intended statement |
|---|---|
| `divisor_set_limsup` | For every infinite A⊆ℕ and every k∈ℕ, limsup_{x→∞} (max_{n<x} d_A(n)) / (∑_{a∈A, a<x} 1/a)^k = ∞. |

**Not sufficient for prize_ready:** weaker special cases, finite truncations, or intermediate lemmas alone.

## Checklist (all must pass)

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit` in all `*.lean` (excluding `.lake`)
- [ ] `#print axioms` on headline theorem(s) shows only standard axioms
- [ ] Public repo HEAD is a full 40-character commit SHA
- [ ] README documents build instructions
- [ ] `formalization.yaml` and/or `ATTRIBUTION.md` name `Yi-111-a` / operators
- [ ] Named headline theorem(s) above exist and are proved

## Harness rule

`prize_ready=true` **only** when every checklist item passes **and** the named headline theorem(s) exist and are proved.
