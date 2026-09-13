# Albertson conjecture verification

Exact ancillary verification for the manuscript `A proof of Albertson's Conjecture`.

## Requirements

- Python 3.10+
- a C++17 compiler (`g++` or `clang++`)
- no third-party Python packages, solver, CAS, or network access

## Run

```text
python verify.py
```

Set `ALBERTSON_THREADS` to limit CPU use. A successful run ends with

```text
ALL CERTIFICATES VERIFIED
```

## What is checked

The verifier treats the certificate files as untrusted witnesses. It checks their
SHA-256 hashes, validates record domains and rational
denominators, rejects duplicate finite-near keys and malformed sampling records,
reconstructs every certified case, and evaluates all finite inequalities with exact
integer/rational arithmetic. The uniform `r >= 1000` certificate is checked with
exact rational inclusion arithmetic and exact consecutive interval coverage.

The three certificates are:

- `cert/near_residual.bin`: residual near-range cases for `19 <= r <= 999`;
- `cert/middle_19_999.rle`: every finite middle-range case for `19 <= r <= 999`;
- `cert/tail_R1000.bin`: the uniform middle-range interval cover for `r >= 1000`.

The published `r <= 18` theorem, the external order reduction, the analytic near-tail
argument, and the proofs reducing successful certificate checks to the main theorem
remain mathematical parts of the manuscript.
