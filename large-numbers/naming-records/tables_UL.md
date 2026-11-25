## System UL: names of size <= 12, proof length <= 10,000,000

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
| 9 | 8 | 8 | 10 | 16 | 27 | 27 | 27 | 27 | 27 | 8 |
| 10 | 9 | 9 | 12 | 17 | 32 | 81 | 81 | 81 | 81 | 9 |
| 11 | 9 | 10 | 13 | 18 | 36 | 82 | 125 | 256 | 256 | 10 |
| 12 | 9 | 11 | 14 | 20 | 37 | 83 | 128 | 257 | 1024 | 11 |
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
| 8 | 7 | `(SSS0^SS0)` = 3^2 | 9 | 939 | 9 | `(SSS0^SS0)` = 3^2 | 939 |
| 9 | 8 | `(SSS0*SSS0)` = 3*3 | 9 | 610 | 27 | `(SSS0^SSS0)` = 3^3 | 4,046 |
| 10 | 9 | `S(SSS0*SSS0)` = S(3*3) | 10 | 631 | 81 | `(SSS0^SSSS0)` = 3^4 | 25,998 |
| 11 | 10 | `SS(SSS0*SSS0)` = S(S(3*3)) | 11 | 654 | 256 | `(SSSS0^SSSS0)` = 4^4 | 220,280 |
| 12 | 11 | `SSS(SSS0*SSS0)` = S(S(S(3*3))) | 12 | 679 | 1024 | `(SSSS0^SSSSS0)` = 4^5 | 3,385,628 |

### 3. The record as the budget grows (names of size <= 12)

Every budget at which the record goes up, after the numerals run out.

| budget t | record k | log2 k | witness | size | steps |
|---|---|---|---|---|---|
| 12 | 11 | 3.46 | `SSSSSSSSSSS0` = 11 | 12 | 0 |
| 679 | 12 | 3.58 | `SSS(SSS0*SSS0)` = S(S(S(3*3))) | 12 | 28 |
| 859 | 13 | 3.70 | `S(SSSSSS0*SS0)` = S(6*2) | 12 | 30 |
| 939 | 14 | 3.81 | `SS(SSSS0*SSS0)` = S(S(4*3)) | 12 | 33 |
| 1,218 | 15 | 3.91 | `(SSSSS0*SSS0)` = 5*3 | 11 | 37 |
| 1,247 | 16 | 4.00 | `S(SSSSS0*SSS0)` = S(5*3) | 12 | 38 |
| 1,436 | 17 | 4.09 | `S(SSSS0*SSSS0)` = S(4*4) | 12 | 42 |
| 1,603 | 18 | 4.17 | `(SSSSSS0*SSS0)` = 6*3 | 12 | 43 |
| 1,949 | 19 | 4.25 | `SSS(SSSS0^SS0)` = S(S(S(4^2))) | 12 | 62 |
| 1,961 | 20 | 4.32 | `(SSSSS0*SSSS0)` = 5*4 | 12 | 49 |
| 3,467 | 25 | 4.64 | `(SSSSS0^SS0)` = 5^2 | 10 | 83 |
| 3,505 | 26 | 4.70 | `S(SSSSS0^SS0)` = S(5^2) | 11 | 84 |
| 3,545 | 27 | 4.75 | `SS(SSSSS0^SS0)` = S(S(5^2)) | 12 | 85 |
| 4,085 | 28 | 4.81 | `S(SSS0^SSS0)` = S(3^3) | 10 | 96 |
| 4,126 | 29 | 4.86 | `SS(SSS0^SSS0)` = S(S(3^3)) | 11 | 97 |
| 4,169 | 30 | 4.91 | `SSS(SSS0^SSS0)` = S(S(S(3^3))) | 12 | 98 |
| 6,046 | 32 | 5.00 | `(SS0^SSSSS0)` = 2^5 | 10 | 125 |
| 6,091 | 33 | 5.04 | `S(SS0^SSSSS0)` = S(2^5) | 11 | 126 |
| 6,096 | 36 | 5.17 | `(SSSSSS0^SS0)` = 6^2 | 11 | 111 |
| 6,146 | 37 | 5.21 | `S(SSSSSS0^SS0)` = S(6^2) | 12 | 112 |
| 10,151 | 49 | 5.61 | `(SSSSSSS0^SS0)` = 7^2 | 12 | 143 |
| 16,297 | 64 | 6.00 | `(SSSS0^SSS0)` = 4^3 | 10 | 189 |
| 16,374 | 65 | 6.02 | `S(SSSS0^SSS0)` = S(4^3) | 11 | 190 |
| 16,453 | 66 | 6.04 | `SS(SSSS0^SSS0)` = S(S(4^3)) | 12 | 191 |
| 25,185 | 81 | 6.34 | `((SSS0^SS0)^SS0)` = (3^2)^2 | 12 | 238 |
| 26,092 | 82 | 6.36 | `S(SSS0^SSSS0)` = S(3^4) | 11 | 248 |
| 26,188 | 83 | 6.38 | `SS(SSS0^SSSS0)` = S(S(3^4)) | 12 | 249 |
| 54,626 | 125 | 6.97 | `(SSSSS0^SSS0)` = 5^3 | 11 | 335 |
| 54,765 | 126 | 6.98 | `S(SSSSS0^SSS0)` = S(5^3) | 12 | 336 |
| 68,867 | 128 | 7.00 | `(SS0^SSSSSSS0)` = 2^7 | 12 | 425 |
| 153,701 | 216 | 7.75 | `(SSSSSS0^SSS0)` = 6^3 | 12 | 545 |
| 208,155 | 243 | 7.92 | `(SSS0^SSSSS0)` = 3^5 | 11 | 687 |
| 208,412 | 244 | 7.93 | `S(SSS0^SSSSS0)` = S(3^5) | 12 | 688 |
| 220,280 | 256 | 8.00 | `(SSSS0^SSSS0)` = 4^4 | 11 | 679 |
| 220,550 | 257 | 8.01 | `S(SSSS0^SSSS0)` = S(4^4) | 12 | 680 |
| 1,011,325 | 512 | 9.00 | `(SS0^(SSS0^SS0))` = 2^(3^2) | 12 | 1,614 |
| 1,245,330 | 625 | 9.29 | `(SSSSS0^SSSS0)` = 5^4 | 12 | 1,547 |
| 1,804,037 | 729 | 9.51 | `(SSS0^SSSSSS0)` = 3^6 | 12 | 1,991 |
| 3,385,628 | 1024 | 10.00 | `(SSSS0^SSSSS0)` = 4^5 | 12 | 2,609 |

### 4. Cheapest names: D(k) = size + log2(proof length)

Every k from 0 to 20 has a name of size <= 12. `K(k)` = least name size, proof free. `D(k)` = least size + log2(proof). `N(k)` = the numeral's own cost, size + log2(size).

35 numbers have a name that beats their own numeral on `D` (the smallest is 16); every other number named here is named most cheaply by its numeral. The 20 with the largest saving:

| k | numeral cost N(k) | D(k) | saving | best name | size | proof length | K(k) |
|---|---|---|---|---|---|---|---|
| 1024 | 1035.00 | 33.69 | 1001.31 | `(SSSS0^SSSSS0)` = 4^5 | 12 | 3,385,628 | 12 |
| 729 | 739.51 | 32.78 | 706.73 | `(SSS0^SSSSSS0)` = 3^6 | 12 | 1,804,037 | 12 |
| 625 | 635.29 | 32.25 | 603.04 | `(SSSSS0^SSSS0)` = 5^4 | 12 | 1,245,330 | 12 |
| 512 | 522.00 | 31.95 | 490.05 | `(SS0^(SSS0^SS0))` = 2^(3^2) | 12 | 1,011,325 | 12 |
| 257 | 266.01 | 29.75 | 236.26 | `S(SSSS0^SSSS0)` = S(4^4) | 12 | 220,550 | 12 |
| 256 | 265.01 | 28.75 | 236.26 | `(SSSS0^SSSS0)` = 4^4 | 11 | 220,280 | 11 |
| 244 | 252.94 | 29.67 | 223.27 | `S(SSS0^SSSSS0)` = S(3^5) | 12 | 208,412 | 12 |
| 243 | 251.93 | 28.67 | 223.26 | `(SSS0^SSSSS0)` = 3^5 | 11 | 208,155 | 11 |
| 216 | 224.76 | 29.23 | 195.53 | `(SSSSSS0^SSS0)` = 6^3 | 12 | 153,701 | 12 |
| 128 | 136.01 | 28.07 | 107.94 | `(SS0^SSSSSSS0)` = 2^7 | 12 | 68,867 | 12 |
| 126 | 133.99 | 27.74 | 106.25 | `S(SSSSS0^SSS0)` = S(5^3) | 12 | 54,765 | 12 |
| 125 | 132.98 | 26.74 | 106.24 | `(SSSSS0^SSS0)` = 5^3 | 11 | 54,626 | 11 |
| 83 | 90.39 | 26.68 | 63.72 | `SS(SSS0^SSSS0)` = S(S(3^4)) | 12 | 26,188 | 12 |
| 82 | 89.38 | 25.67 | 63.70 | `S(SSS0^SSSS0)` = S(3^4) | 11 | 26,092 | 11 |
| 81 | 88.36 | 24.67 | 63.69 | `(SSS0^SSSS0)` = 3^4 | 10 | 25,998 | 10 |
| 66 | 73.07 | 26.01 | 47.06 | `SS(SSSS0^SSS0)` = S(S(4^3)) | 12 | 16,453 | 12 |
| 65 | 72.04 | 25.00 | 47.05 | `S(SSSS0^SSS0)` = S(4^3) | 11 | 16,374 | 11 |
| 64 | 71.02 | 23.99 | 47.03 | `(SSSS0^SSS0)` = 4^3 | 10 | 16,297 | 10 |
| 49 | 55.64 | 25.31 | 30.33 | `(SSSSSSS0^SS0)` = 7^2 | 12 | 10,151 | 12 |
| 37 | 43.25 | 24.59 | 18.66 | `S(SSSSSS0^SS0)` = S(6^2) | 12 | 6,146 | 12 |

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

