#!/usr/bin/env python3
"""Exhaustively sanity-check the challenge's finite probability formulas.

Uses Python's standard library and exact rational arithmetic. These small models
check indexing/rounding and graph laws, not the asymptotic theorem or Lean code.
"""

import argparse
from fractions import Fraction as F
import itertools
import json
import math
from pathlib import Path


def check_case(n, q, length):
    edges = list(itertools.combinations(range(n), 2))
    count = len(edges)
    colorable = [
        any(all(not (mask >> i & 1) or coloring[u] != coloring[v]
                for i, (u, v) in enumerate(edges))
            for coloring in itertools.product(range(q), repeat=n))
        for mask in range(1 << count)
    ]
    total = count ** length
    surviving, first = [0] * (length + 1), [0] * (length + 1)
    for sequence in itertools.product(range(count), repeat=length):
        mask, failure = 0, None
        for m in range(length + 1):
            if m:
                mask |= 1 << sequence[m - 1]
            if colorable[mask]:
                surviving[m] += 1
            elif failure is None:
                failure = m
                first[m] += 1
    survival = [F(value, total) for value in surviving]
    mass = [survival[k] - survival[k + 1] for k in range(length)]
    if any(mass[k] != F(first[k + 1], total) for k in range(length)):
        raise ValueError("survival differences do not give first-failure masses")
    windows = 0
    for center in range(-3, 9):
        for width in [F(-1), F(0), F(1, 4), F(1, 2), F(3, 4), F(1), F(5, 4), F(5, 2)]:
            upper = max(0, math.floor(center + width))
            if upper > length:
                continue
            counted = sum((mass[k] for k in range(upper)
                           if abs(F(k + 1) - center) <= width), F(0))
            direct = sum((F(first[h], total) for h in range(1, length + 1)
                          if abs(F(h) - center) <= width), F(0))
            lower = max(1, math.ceil(center - width))
            upper_integer = math.floor(center + width)
            telescoped = survival[lower - 1] - survival[upper_integer] if lower <= upper_integer else F(0)
            if counted != direct or counted != telescoped:
                raise ValueError(f"window discrepancy: {n=}, {q=}, {center=}, {width=}")
            windows += 1
    for probability in [F(0), F(1, 4), F(1, 2), F(3, 4), F(1)]:
        weights = [probability ** mask.bit_count() * (1 - probability) ** (count - mask.bit_count())
                   for mask in range(1 << count)]
        if sum(weights) != 1:
            raise ValueError("Bernoulli graph weights do not sum to one")
        direct = sum((weight for mask, weight in enumerate(weights) if colorable[mask]), F(0))
        mixed = F(0)
        for m in range(count + 1):
            choices = [mask for mask in range(1 << count) if mask.bit_count() == m]
            uniform = F(sum(colorable[mask] for mask in choices), len(choices))
            mixed += math.comb(count, m) * probability ** m * (1 - probability) ** (count - m) * uniform
        if direct != mixed:
            raise ValueError("Bernoulli and binomial mixtures of fixed-edge laws disagree")
    return {"n": n, "q": q, "prefix_length": length, "sequences": total,
            "window_checks": windows, "bernoulli_probability_checks": 5,
            "survival": list(map(str, survival)), "hitting_mass": list(map(str, mass)), "status": "PASS"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=Path, default=Path("verification/submission/finite-model-check.json"))
    args = parser.parse_args()
    result = {"scope": "Small finite-model sanity checks; not an asymptotic proof or Lean check",
              "cases": [check_case(3, 2, 7), check_case(4, 3, 7)], "status": "PASS"}
    root = Path(__file__).resolve().parents[1]
    report = args.report if args.report.is_absolute() else root / args.report
    report.parent.mkdir(parents=True, exist_ok=True)
    report.write_text(json.dumps(result, indent=2) + "\n")
    print("PASS: 282123 edge sequences; 170 windows; 10 Bernoulli mixture checks")


if __name__ == "__main__":
    main()
