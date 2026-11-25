## System U: names of size <= 12, proof length <= 10,000,000

493,800 names have a proof within the cap.

### 1. Record: largest k named by a name of size <= n with proof length <= t

| n \ t | 10 | 100 | 1,000 | 3,000 | 10,000 | 30,000 | 100,000 | 1,000,000 | 10,000,000 | numeral alone |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| 2 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |
| 3 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| 4 | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3 |
| 5 | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4 |
| 6 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 | 5 |
| 7 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 | 6 |
| 8 | 7 | 7 | 9 | 9 | 9 | 9 | 9 | 9 | 9 | 7 |
| 9 | 8 | 8 | 16 | 27 | 27 | 27 | 27 | 27 | 27 | 8 |
| 10 | 9 | 9 | 17 | 32 | 81 | 81 | 81 | 81 | 81 | 9 |
| 11 | 9 | 10 | 18 | 36 | 82 | 125 | 256 | 256 | 256 | 10 |
| 12 | 9 | 11 | 20 | 37 | 83 | 128 | 257 | 729 | 1024 | 11 |
| Prop. 1 cap | 9 | 99 | 999 | 2999 | 9999 | 29999 | 99999 | 999999 | 9999999 | |

### 2. When does a compound name first beat the numeral?

For each name size n: the cheapest proof of any name of size <= n whose value exceeds the largest numeral of size <= n, and the largest number nameable at that size given unlimited budget (within the cap).

| n | numeral record | first beaten by | its value | proof length | largest k at size n | its name | its proof length |
|---|---|---|---|---|---|---|---|
| 1 | 0 | – | – | – | 0 | `0` = 0 | 1 |
| 2 | 1 | – | – | – | 1 | `S0` = 1 | 2 |
| 3 | 2 | – | – | – | 2 | `SS0` = 2 | 3 |
| 4 | 3 | – | – | – | 3 | `SSS0` = 3 | 4 |
| 5 | 4 | – | – | – | 4 | `SSSS0` = 4 | 5 |
| 6 | 5 | – | – | – | 5 | `SSSSS0` = 5 | 6 |
| 7 | 6 | – | – | – | 6 | `SSSSSS0` = 6 | 7 |
| 8 | 7 | `(SSS0^SS0)` = 3^2 | 9 | 412 | 9 | `(SSS0^SS0)` = 3^2 | 412 |
| 9 | 8 | `(SSS0*SSS0)` = 3*3 | 9 | 238 | 27 | `(SSS0^SSS0)` = 3^3 | 1,664 |
| 10 | 9 | `(SSSSS0*SS0)` = 5*2 | 10 | 227 | 81 | `(SSS0^SSSS0)` = 3^4 | 9,572 |
| 11 | 10 | `S(SSSSS0*SS0)` = S(5*2) | 11 | 243 | 256 | `(SSSS0^SSSS0)` = 4^4 | 76,189 |
| 12 | 11 | `SS(SSSSS0*SS0)` = S(S(5*2)) | 12 | 259 | 1024 | `(SSSS0^SSSSS0)` = 4^5 | 1,141,980 |

### 3. The record as the budget grows (names of size <= 12)

Every budget at which the record goes up, after the numerals run out.

| budget t | record k | log2 k | witness | size | steps |
|---|---|---|---|---|---|
| 12 | 11 | 3.46 | `SSSSSSSSSSS0` = 11 | 12 | 0 |
| 259 | 12 | 3.58 | `SS(SSSSS0*SS0)` = S(S(5*2)) | 12 | 15 |
| 309 | 13 | 3.70 | `S(SSSSSS0*SS0)` = S(6*2) | 12 | 17 |
| 363 | 14 | 3.81 | `(SSSSSSS0*SS0)` = 7*2 | 12 | 19 |
| 456 | 15 | 3.91 | `(SSSSS0*SSS0)` = 5*3 | 11 | 22 |
| 479 | 16 | 4.00 | `S(SSSSS0*SSS0)` = S(5*3) | 12 | 22 |
| 588 | 17 | 4.09 | `S(SSSS0*SSSS0)` = S(4*4) | 12 | 25 |
| 592 | 18 | 4.17 | `(SSSSSS0*SSS0)` = 6*3 | 12 | 25 |
| 765 | 20 | 4.32 | `(SSSSS0*SSSS0)` = 5*4 | 12 | 29 |
| 1,518 | 25 | 4.64 | `(SSSSS0^SS0)` = 5^2 | 10 | 55 |
| 1,574 | 26 | 4.70 | `S(SSSSS0^SS0)` = S(5^2) | 11 | 55 |
| 1,630 | 27 | 4.75 | `SS(SSSSS0^SS0)` = S(S(5^2)) | 12 | 55 |
| 1,729 | 28 | 4.81 | `S(SSS0^SSS0)` = S(3^3) | 10 | 64 |
| 1,794 | 29 | 4.86 | `SS(SSS0^SSS0)` = S(S(3^3)) | 11 | 64 |
| 1,859 | 30 | 4.91 | `SSS(SSS0^SSS0)` = S(S(S(3^3))) | 12 | 64 |
| 2,598 | 32 | 5.00 | `(SS0^SSSSS0)` = 2^5 | 10 | 93 |
| 2,623 | 36 | 5.17 | `(SSSSSS0^SS0)` = 6^2 | 11 | 71 |
| 2,695 | 37 | 5.21 | `S(SSSSSS0^SS0)` = S(6^2) | 12 | 71 |
| 4,284 | 49 | 5.61 | `(SSSSSSS0^SS0)` = 7^2 | 12 | 89 |
| 6,171 | 64 | 6.00 | `(SSSS0^SSS0)` = 4^3 | 10 | 115 |
| 6,287 | 65 | 6.02 | `S(SSSS0^SSS0)` = S(4^3) | 11 | 115 |
| 6,403 | 66 | 6.04 | `SS(SSSS0^SSS0)` = S(S(4^3)) | 12 | 115 |
| 9,572 | 81 | 6.34 | `(SSS0^SSSS0)` = 3^4 | 10 | 153 |
| 9,726 | 82 | 6.36 | `S(SSS0^SSSS0)` = S(3^4) | 11 | 153 |
| 9,880 | 83 | 6.38 | `SS(SSS0^SSSS0)` = S(S(3^4)) | 12 | 153 |
| 19,762 | 125 | 6.97 | `(SSSSS0^SSS0)` = 5^3 | 11 | 192 |
| 19,955 | 126 | 6.98 | `S(SSSSS0^SSS0)` = S(5^3) | 12 | 192 |
| 26,001 | 128 | 7.00 | `(SS0^SSSSSSS0)` = 2^7 | 12 | 297 |
| 54,203 | 216 | 7.75 | `(SSSSSS0^SSS0)` = 6^3 | 12 | 301 |
| 72,358 | 243 | 7.92 | `(SSS0^SSSSS0)` = 3^5 | 11 | 404 |
| 72,763 | 244 | 7.93 | `S(SSS0^SSSSS0)` = S(3^5) | 12 | 404 |
| 76,189 | 256 | 8.00 | `(SSSS0^SSSS0)` = 4^4 | 11 | 381 |
| 76,571 | 257 | 8.01 | `S(SSSS0^SSSS0)` = S(4^4) | 12 | 381 |
| 364,998 | 512 | 9.00 | `(SS0^(SSS0^SS0))` = 2^(3^2) | 12 | 1,106 |
| 422,466 | 625 | 9.29 | `(SSSSS0^SSSS0)` = 5^4 | 12 | 829 |
| 614,624 | 729 | 9.51 | `(SSS0^SSSSSS0)` = 3^6 | 12 | 1,141 |
| 1,141,980 | 1024 | 10.00 | `(SSSS0^SSSSS0)` = 4^5 | 12 | 1,415 |

### 4. Cheapest names: D(k) = size + log2(proof length)

Every k from 0 to 20 has a name of size <= 12. `K(k)` = least name size, proof free. `D(k)` = least size + log2(proof). `N(k)` = the numeral's own cost, size + log2(size).

36 numbers have a name that beats their own numeral on `D` (the smallest is 15); every other number named here is named most cheaply by its numeral. The 20 with the largest saving:

| k | numeral cost N(k) | D(k) | saving | best name | size | proof length | K(k) |
|---|---|---|---|---|---|---|---|
| 1024 | 1035.00 | 32.12 | 1002.88 | `(SSSS0^SSSSS0)` = 4^5 | 12 | 1,141,980 | 12 |
| 729 | 739.51 | 31.23 | 708.28 | `(SSS0^SSSSSS0)` = 3^6 | 12 | 614,624 | 12 |
| 625 | 635.29 | 30.69 | 604.60 | `(SSSSS0^SSSS0)` = 5^4 | 12 | 422,466 | 12 |
| 512 | 522.00 | 30.48 | 491.53 | `(SS0^(SSS0^SS0))` = 2^(3^2) | 12 | 364,998 | 12 |
| 256 | 265.01 | 27.22 | 237.79 | `(SSSS0^SSSS0)` = 4^4 | 11 | 76,189 | 11 |
| 257 | 266.01 | 28.22 | 237.79 | `S(SSSS0^SSSS0)` = S(4^4) | 12 | 76,571 | 12 |
| 243 | 251.93 | 27.14 | 224.79 | `(SSS0^SSSSS0)` = 3^5 | 11 | 72,358 | 11 |
| 244 | 252.94 | 28.15 | 224.79 | `S(SSS0^SSSSS0)` = S(3^5) | 12 | 72,763 | 12 |
| 216 | 224.76 | 27.73 | 197.04 | `(SSSSSS0^SSS0)` = 6^3 | 12 | 54,203 | 12 |
| 128 | 136.01 | 26.67 | 109.34 | `(SS0^SSSSSSS0)` = 2^7 | 12 | 26,001 | 12 |
| 125 | 132.98 | 25.27 | 107.71 | `(SSSSS0^SSS0)` = 5^3 | 11 | 19,762 | 11 |
| 126 | 133.99 | 26.28 | 107.70 | `S(SSSSS0^SSS0)` = S(5^3) | 12 | 19,955 | 12 |
| 81 | 88.36 | 23.22 | 65.13 | `(SSS0^SSSS0)` = 3^4 | 10 | 9,572 | 10 |
| 82 | 89.38 | 24.25 | 65.13 | `S(SSS0^SSSS0)` = S(3^4) | 11 | 9,726 | 11 |
| 83 | 90.39 | 25.27 | 65.12 | `SS(SSS0^SSSS0)` = S(S(3^4)) | 12 | 9,880 | 12 |
| 64 | 71.02 | 22.59 | 48.43 | `(SSSS0^SSS0)` = 4^3 | 10 | 6,171 | 10 |
| 65 | 72.04 | 23.62 | 48.43 | `S(SSSS0^SSS0)` = S(4^3) | 11 | 6,287 | 11 |
| 66 | 73.07 | 24.64 | 48.42 | `SS(SSSS0^SSS0)` = S(S(4^3)) | 12 | 6,403 | 12 |
| 49 | 55.64 | 24.06 | 31.58 | `(SSSSSSS0^SS0)` = 7^2 | 12 | 4,284 | 12 |
| 36 | 42.21 | 22.36 | 19.85 | `(SSSSSS0^SS0)` = 6^2 | 11 | 2,623 | 11 |

### 5. Largest number per naming cost

For each d: the largest k with `D(k) <= d`, and the largest with `K(k) <= d` (proof free). A name of size s has `D >= s + log2 s`, so the D column is complete (no larger name could enter) for d < 16.7; beyond that it is a lower bound. The K column is complete only for d <= 12.

| d | largest k, D(k) <= d | name | size | proof | largest k, K(k) <= d |
|---|---|---|---|---|---|
| 2 | 0 | `0` = 0 | 1 | 1 | 1 |
| 3 | 1 | `S0` = 1 | 2 | 2 | 2 |
| 4 | 1 | `S0` = 1 | 2 | 2 | 3 |
| 5 | 2 | `SS0` = 2 | 3 | 3 | 4 |
| 6 | 3 | `SSS0` = 3 | 4 | 4 | 5 |
| 7 | 3 | `SSS0` = 3 | 4 | 4 | 6 |
| 8 | 4 | `SSSS0` = 4 | 5 | 5 | 9 |
| 9 | 5 | `SSSSS0` = 5 | 6 | 6 | 27 |
| 10 | 6 | `SSSSSS0` = 6 | 7 | 7 | 81 |
| 11 | 7 | `SSSSSSS0` = 7 | 8 | 8 | 256 |
| 12 | 7 | `SSSSSSS0` = 7 | 8 | 8 | 1024 |
| 13 | 8 | `SSSSSSSS0` = 8 | 9 | 9 | – |
| 14 | 9 | `SSSSSSSSS0` = 9 | 10 | 10 | – |
| 15 | 10 | `SSSSSSSSSS0` = 10 | 11 | 11 | – |
| 16 | 11 | `SSSSSSSSSSS0` = 11 | 12 | 12 | – |

### 6. Evaluation proof versus shortest proof in any order

For the 2,264 names of size <= 8 with evaluation proof <= 500: the exhaustive search finished for 2,262; the evaluation proof is the shortest for 1,906 of those. Largest ratio: `(0^S(S0^S0))`, evaluation 62 vs shortest 18.

Record-table cells (n <= 8, t <= 500) that change if shortest proofs are used: none.

