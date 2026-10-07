# SHA-256 vectors

The response files come from [NIST's byte-oriented SHA test suite](https://csrc.nist.gov/projects/cryptographic-algorithm-validation-program/secure-hashing).
They contain 65 short-message answers, 64 long-message answers, and 100 Monte Carlo answers.
The Monte Carlo procedure follows [SHAVS](https://csrc.nist.gov/csrc/media/projects/cryptographic-algorithm-validation-program/documents/shs/shavs.pdf), section 6.4.

The regression runner also checks the three [FIPS 180-2 appendix B examples](https://csrc.nist.gov/files/pubs/fips/180-2/upd1/final/docs/fips180-2withchangenotice.pdf) and [NIST's intermediate values](https://csrc.nist.gov/csrc/media/projects/cryptographic-standards-and-guidelines/documents/examples/sha256.pdf).
All fixtures are embedded at build time.
