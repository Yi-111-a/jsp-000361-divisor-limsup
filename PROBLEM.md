# JSP-000361 — For a fixed infinite integer set, how many divisors of a single integer can belong to that set?

- **id:** JSP-000361
- **title:** For a fixed infinite integer set, how many divisors of a single integer can belong to that set?
- **area:** Number theory / Divisors
- **status:** Solved
- **Lean:** No (formalization target)
- **Eligible / Claim:** No / Unavailable
- **role:** Formalize path (Solved + Lean=No)

## Statement

For a fixed infinite integer set, how many divisors of a single integer can belong to that set?

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000361
- Awards home: https://github.com/TheJustinSunPrize/awards

## Primary papers

- Erdős–Sárközy (ErSa80), Studia Sci. Math. Hungar. (1980), 467–479

## Accepted mathematical answer

Let A⊆ℕ be infinite and d_A(n) = #{a∈A : a|n}. Erdős–Sárközy (ErSa80) proved that for every k, limsup_{x→∞} max_{n<x} d_A(n) / (∑_{a∈A∩[1,x)} 1/a)^k = ∞.

## Success criteria

- `lake build` succeeds
- Zero `sorry` / `admit`
- Named headline theorem(s) in ACCEPTANCE.md proved
