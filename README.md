# JSP-000301 — Lean 4 formalization

Formal Lean 4 proof for **entry JSP-000301** of [The Justin Sun Prize](https://github.com/TheJustinSunPrize/awards) problem bank.

## The problem

> If two consecutive positive integers are powerful, must at least one be a perfect square?

## The answer: **No.**

Counterexample (machine-checked in this repository):

- 12167 = 23^3 — powerful (23^2 divides 23^3), NOT a square
- 12168 = 2^3 · 3^2 · 13^2 — powerful (2^2 | 2^3, 3^2 | 3^2, 13^2 | 13^2), NOT a square
- 12167 + 1 = 12168

## What is proved

```lean
theorem jsp_000301 :
    ∃ a b : Nat, a + 1 = b ∧ Powerful a ∧ Powerful b ∧ ¬ IsSquare a ∧ ¬ IsSquare b
```

`Powerful n` means every prime divisor p of n satisfies p * p ∣ n
(primality defined by explicit trial division, decided mechanically inside the proof).

## Verification

**Fully self-contained**: bare Lean 4, no Mathlib, no Batteries, no axiom, no sorry.

```bash
lean JSP000301.lean        # Lean 4.34.0 — exits with zero errors
```

All finite divisor-classification checks are fully discharged in the standard Lean 4 kernel via `decide` over `p < 12168` (kernel reduction, zero TCB expansion, no `native_decide`, axioms: `[propext, Quot.sound]`).

## Provenance

- Mathematical content: the counterexample is classical (Golomb, Powerful
  numbers, Amer. Math. Monthly 77 (1970) 848-855; Walsh, Consecutive integer
  pairs of powerful numbers and related Diophantine equations, Fibonacci
  Quart. 14 (1976) 111-116; Guy, Unsolved Problems in Number Theory, 3rd ed.
  2004). This repository does **not** claim the mathematical discovery.
- Formalization: produced with AI assistance (Claude via WorkBuddy) operated by
  @Neo7672, 2026-09-16. Submitted to The Justin Sun Prize as the Lean
  formalization component of entry JSP-000301.
