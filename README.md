# Albertson verification

Ancillary exact verification for the computer-assisted claims in the manuscript.
The manuscript contains the mathematical reductions and proves why these checks
are sufficient.

## Requirements

- Python 3.10+
- C++17 compiler: `g++` or `clang++`
- no third-party Python packages
- no solver, CAS, Boost, or network access

## Run

```text
python verify.py
```

Set `ALBERTSON_THREADS` to limit CPU use if desired.

A successful run ends with

```text
ALL CERTIFICATES VERIFIED
```

The certificate files are treated as untrusted witnesses. The verifier checks
file integrity, parses the complete certified domains, reconstructs the required
finite near and middle cases, checks every exact integer/rational inequality,
checks that no residual near witness is missing or unused, and checks consecutive
coverage of the uniform `r >= 1000` middle-range interval certificate.

The three certificates correspond to:

- `cert/near_residual.bin`: residual finite near-range cases inside `19 <= r <= 999`;
- `cert/middle_19_999.rle`: every integer middle-range case for `19 <= r <= 999`;
- `cert/tail_R1000.bin`: exact rational interval cover for the uniform middle range `r >= 1000`.

The published theorem for `r <= 18`, the order reductions, the analytic near-tail
argument, and the implication from successful certificate verification to the
main theorem are mathematical parts of the manuscript rather than trusted code.
