# deterministic-group-actions-magma

Magma code accompanying my Master's thesis (Faculty of Science, 2025-2026)
on post-quantum commutative group actions from orientations of large
discriminant, following Marc Houben's work
([ePrint 2025/1098](https://eprint.iacr.org/2025/1098)).

The repository has two folders.

`literal_sage_adaptation/` is an as-close-as-possible transcription of
Houben's SageMath proof-of-concept
([houbenmr/LargeDiscriminantOrientations](https://github.com/houbenmr/LargeDiscriminantOrientations)).
It contains the 256-bit and 512-bit versions.

`optimised/` is the optimised Magma implementation of the same group action.
The Vélu and √élu isogenies are based on the C code from
[dCTIDH](https://github.com/PaZeZeVaAt/dCTIDH/), and the tail-pruning in the
shared-secret derivation is done as in
[wwwwweize/OSIDH-LD](https://github.com/wwwwweize/OSIDH-LD)
([ePrint 2026/627](https://eprint.iacr.org/2026/627)). It contains all four
instantiations below. The field-operation cycle counts used in the cost model
were measured with Michael Scott's
[modarith](https://github.com/mcarrickscott/modarith), compiled with gcc
(`-O3 -march=native -mtune=native`).

## Instantiations

Each benchmark fixes a prime `p` and an orientation `σ`. In the table, `r` is
the number of tuples in the full kernel representation of `σ` and the discriminant column is the bit-size
of `|Disc(σ)|`. All but the 515-bit one use the twist trick.

| benchmark | prime `p` | orientation | discriminant | twist |
|---|---|---|---|---|
| `bench_256` | 255-bit | r = 13 | ~4047 bits | yes |
| `bench_256_r7` | 256-bit | r = 7 | ~2212 bits | yes |
| `bench_256_r13` | 256-bit | r = 13 | ~4106 bits | yes |
| `bench_512` | 515-bit | r = 8 | ~4103 bits | no |

`bench_256_r7` and `bench_256_r13` are the same 256-bit prime with two
orientations; `r = 13` is the reference example from Houben's paper.
`bench_256` is a separate 255-bit prime.

## Running

The different instantiations can be run by running their benchmark scripts e.g. 

```magma
load "optimised/bench_256_r13.m";
```

`optimised/` has all four (`bench_256`, `bench_256_r7`, `bench_256_r13`,
`bench_512`); `literal_sage_adaptation/` has the 256-bit and 512-bit versions.

## References

- M. Houben, *Efficient Post-quantum Commutative Group Actions from
  Orientations of Large Discriminant*,
  [ePrint 2025/1098](https://eprint.iacr.org/2025/1098). The paper this thesis
  builds on and the source of `literal_sage_adaptation/`.
- Tail-pruning follows
  [wwwwweize/OSIDH-LD](https://github.com/wwwwweize/OSIDH-LD) and
  [ePrint 2026/627](https://eprint.iacr.org/2026/627).
- The isogeny code is based on the C implementation in
  [dCTIDH](https://github.com/PaZeZeVaAt/dCTIDH/).
- Field-operation cycle counts were derived from Michael Scott's
  [modarith](https://github.com/mcarrickscott/modarith).

## Copyright

This repository contains work carried out as part of a Master's thesis at
KU Leuven, Faculty of Science, academic year 2025-2026.

> Without written permission of the supervisor(s) and the author it is
> forbidden to reproduce or adapt in any form or by any means any part of
> this publication. Requests for obtaining the right to reproduce or utilise
> parts of this publication should be addressed to KU Leuven, Faculty of
> Science, Celestijnenlaan 200H - box 2100, 3001 Leuven (Heverlee), Telephone +32 16 32 14 01.
>
> Written permission from the supervisor is also required to use the methods, products, schematics, and programs described in this work for industrial or commercial use, and for submitting this publication in scientific contests.
