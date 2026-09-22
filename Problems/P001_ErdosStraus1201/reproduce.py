"""Reproduce the six fixed-x searches from Outcasts post #2.

Python 3, standard library only.
Run from the repository root: python3 Problems/P001_ErdosStraus1201/reproduce.py
For each x, enumerate every positive factor pair a*b=(p*x)^2 with a<=b.
The a<=p*x endpoint is exact, not an arbitrary bound on y or z.
"""

import json
import platform


def main():
    p = 1201
    rows = []
    for x in range(301, 307):
        c, m = 4 * x - p, p * x
        solutions = []
        for a in range(1, m + 1):
            if m * m % a:
                continue
            b = m * m // a
            if (a + m) % c or (b + m) % c:
                continue
            y, z = (a + m) // c, (b + m) // c
            lhs = 4 * x * y * z
            rhs = p * (x * y + x * z + y * z)
            assert 0 < x <= y <= z
            assert lhs == rhs
            assert (c * y - m) * (c * z - m) == m * m
            solutions.append({
                "x": x, "y": y, "z": z,
                "factor_a": a, "factor_b": b,
                "integer_lhs": lhs, "integer_rhs": rhs,
            })
        rows.append({"p": p, "x": x, "c": c, "M": m,
                     "solution_count": len(solutions), "solutions": solutions})
    assert [row["solution_count"] for row in rows] == [0, 0, 0, 0, 0, 3]
    print(json.dumps({
        "python_version": platform.python_version(),
        "dependencies": "Python standard library only",
        "inputs": {"p": p, "x_first": 301, "x_last": 306},
        "enumeration": "1 <= a <= M, a divides M^2, b=M^2/a; y<=z",
        "rows": rows,
    }, indent=2))


if __name__ == "__main__":
    main()
