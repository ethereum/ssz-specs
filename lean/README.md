# Lean

A Lean 4 implementation of SSZ, with machine-checked codec and Merkle-tree proofs.
Types are represented as data, so one encoder, decoder, and merkleizer cover the implemented universe.
A native implementation, built on native x86-64 kernels, is proved to compute the same roots, verdicts, and proofs.
The package has no third-party dependencies.

## Reading this package

The executable specification and the proofs about it live in two separate trees, and only the first is meant to be read.

```text
Ssz/            the executable specification, about 3,000 lines
Ssz/Proofs/     the machine-checked properties of it, about 17,000 lines
```

`Ssz/Proofs` mirrors the layout of `Ssz`: what is proved about `Ssz.Codec.Serialize` sits in `Ssz.Proofs.Codec.Serialize`.
Nothing under `Ssz/` imports anything under `Ssz/Proofs/`, and the build enforces that.
An implementer therefore reads `Ssz/` and stops there; [Proven properties](#proven-properties) below says in prose what the other tree establishes.

```text
Ssz/Type      declarations, values, well-formedness, defaults, and paths
Ssz/Codec     serialization, deserialization, the JSON mapping, layouts, roots, and proofs
Ssz/Merkle    bounded and progressive trees, indices, and verification
Ssz/Hash      pure SHA-256
Conformance   readers for the released vectors and for the differential corpus
Tests         independent regression checks
```

## The native implementation

`SszNative/` reads roots, decoding verdicts, nodes, and branches straight from encodings.
It never builds the value an encoding holds.

```text
SszNative/Asm        x86-64 instructions as data, their model, and their printer
SszNative/Kernel     the kernels as programs, and the assembler file they print to
SszNative            hashing, trees, decoding checks, roots, and branches over byte buffers
SszNative/Proofs     the proofs that all of it computes the specification
native/              the printed kernels, and the C bindings that call them
```

Each kernel is a Lean list of x86-64 instructions.
The proofs run that list on a model of the processor.
The emitter prints the same list as assembly.

Three kernels hash pairs of nodes.
One hashes sixteen pairs at once with AVX-512.
The two others use the SHA instructions, on one pair or on two pairs with their rounds interleaved.

Two more kernels gather fields out of records into zero-padded nodes.

Every operation a kernel stands in for has a Lean body, which is its meaning in the logic.
Compiled code calls the kernel where the processor has its instructions, and the Lean body elsewhere.

A declaration can be compiled once into a schema, so that each value read against it skips walking the declaration.
A struct of fixed-size fields, such as a block header, then costs a few copies and one hashing call per tree level.

A long sequence of fixed-size records is rooted as columns: one column per field, hashed across all records at once.
Wide trees and long sequences are split into tasks.
Tasks are pure, so the parallel result is the sequential one by definition.

`native/kernels_x86.S` is committed, so building needs no extra step.
`just lean-kernels` prints it again, and the regressions fail when it is stale.

## Scope

The type universe covers unsigned integers, booleans, byte sequences, bitfields,
vectors, lists, containers, progressive collections, and compatible unions.
Legacy positional unions, including their nullable first option, are not implemented.

The reference is the [SSZ specification at consensus-specs v1.6.1](https://github.com/ethereum/consensus-specs/blob/v1.6.1/ssz/simple-serialize.md),
together with [EIP-7495](https://eips.ethereum.org/EIPS/eip-7495),
[EIP-7916](https://eips.ethereum.org/EIPS/eip-7916), and
[EIP-8016](https://eips.ethereum.org/EIPS/eip-8016).
The current upstream implementation lives in [ethereum/ssz-specs](https://github.com/ethereum/ssz-specs).

Declarations and values are separate data.
Call `Desc.wellFormed` before using an externally supplied declaration.
The low-level operations do not repeat declaration validation at every recursive step.
A successful encoding establishes that its value fits a well-formed declaration.
Proof requests deliberately reject the root itself, empty requests, duplicate indices,
and ancestor/descendant pairs.
This is stricter than the generalized-index arithmetic in the reference proof helpers.

A progressive collection may declare a limit, which rules on its count alone.
The spine is laid out from the data either way, so a declared bound never reaches the root.

For example, a progressive container with layout `[true, false, true]` has two fields.
Its serialization contains only those two fields.
Its Merkle tree contains three positions: the first field, a zero leaf, and the second field.
The layout is mixed into the root so an absent field differs from a present zero-valued field.

### The JSON mapping

An SSZ schema defines a JSON encoding as well as a byte encoding, and both are implemented here.

SSZ gives the byte alias and a one-byte unsigned integer the same type; the JSON mapping does not,
writing the alias as a hex string where it writes the integer as decimal digits in a string.
A declaration alone therefore does not say which document a value is written as, so the mapping
takes a *spelling* beside the declaration: one node per node, marking where the alias was used.
A declaration that never uses the alias needs no spelling of its own.

Only the spelling the mapping gives is accepted, which is stricter than the Python implementation twice:

| The document | Here | The Python implementation |
| --- | --- | --- |
| A bitfield or byte sequence written as an array of its elements | Refused as an element of the wrong kind | Accepted, on all three kinds |
| A hex byte string with no `0x` | Refused | Accepted on a byte array, refused on a bitfield |

Both are leniency in the reference rather than anything the mapping spells, and no vector asserts
either: the invalid vectors that write an array assert only the name the refusal carries.

## Build and test

Generate the local fixtures with `just fill` before running conformance tests.

```bash
just lean-spec     # build the executable specification alone, without its proofs
just lean          # build the package and check its proofs
just lean-test     # run the released vectors and the independent Lean regressions
just lean-parity   # compare generated cases with the Python implementation
just lean-kernels  # print the native kernels from their Lean programs
just lean-bench    # time the native implementation on beacon-chain workloads
```

The toolchain is pinned in `lean-toolchain`.
Warnings are errors, so unfinished proofs fail the build.
The axiom audit checks public and private SSZ declarations automatically.
The build recipe also rejects specification files omitted from the audited import closure,
and rejects a proof module reached from the implementation tree.
CI rebuilds the specification from source and runs the vector, regression, and differential checks.
Only Lean's standard logical axioms are allowed: propositional extensionality,
classical choice, and quotient soundness.
Execution of compiled tests additionally trusts the Lean compiler and runtime.

The released vectors check all six of the formats `fixtures/` carries: byte encodings and their
roots, illegal declarations, generalized indices, JSON documents, single branches, and multiproofs.
Each vector carries its own declaration, so no registry of named types is kept on this side.
The run is held to the case count the release declares, so a vector the walk never reached fails
the run rather than leaving a passing count behind.
Differential tests additionally compare defaults, compatibility, paths, branches, and multiproofs
on types neither implementation was written for.
These vectors are generated by this repository's Python implementation; agreement is not an
independent proof of conformance.
The Lean regressions add independent SHA-256 answers, deep-tree checks, malformed inputs,
and exhaustive canonical re-encoding checks for one- and two-byte inputs across twelve small types.

## Proven properties

- [Codec equivalence](Ssz/Proofs/Codec/Canonicality.lean): encoding and decoding describe the same relation for every well-formed implemented type.
  Values survive round trips, and every accepted byte string is canonical.
- [Admissibility](Ssz/Proofs/Codec/DecodeFits.lean): successful decoding produces a value of the declared shape.
  Successful encoding also establishes admissibility for well-formed declarations.
- [Encoding sizes](Ssz/Proofs/Codec/Size.lean): structural byte counts and the four-byte offset bounds characterize successful serialization of admissible values, with exactly the predicted size.
  An admissible value can fail serialization only through offset overflow.
- [Defaults](Ssz/Proofs/Type/DefaultLaws.lean): every successfully constructed default fits its declaration.
  The executable admissibility check agrees with the logical predicate for well-formed declarations.
- [Compatibility](Ssz/Proofs/Type/CompatibilitySymmetry.lean): checks are reflexive and symmetric, and matching progressive field positions preserve names and compatible types.
  Compatibility is deliberately not transitive, as a checked counterexample demonstrates.
  [Shared addresses](Ssz/Proofs/Type/CompatibilityIndices.lean): compatible progressive containers place a field of one name at one generalized index, so appending fields leaves earlier fields where a proof can still read them.
  Every option a union declares is compatible with every other, and each hangs at the same node whichever option the value carries.
- [Byte aliases](Ssz/Proofs/Codec/Aliases.lean): byte arrays and sequences of eight-bit integers have equal encodings within the composite offset range, and equal roots.
- [Tree construction](Ssz/Proofs/Merkle/Tree.lean): executable bounded and progressive trees agree with their mathematical definitions.
  Padding, subtree extraction, and upward construction preserve roots at arbitrary depths.
  [Merkleization cost](Ssz/Proofs/Merkle/MerkleizeCost.lean): merkleizing a nonempty `k` chunks under a width of `w` costs fewer than `2 * k + log2 w` hashes, so a capacity far above the data adds only its logarithm.
  The hashes counted are the ones the implementation performs, established through a counting twin of the recursion that produces the same root.
  Materializing every leaf instead would cost `w - 1`, which is what the precomputed zero subtrees save.
  [Progressive levels](Ssz/Proofs/Merkle/ProgressiveLevels.lean): a chunk of a progressive collection keeps its index however long the collection grows, and sits three levels deeper per factor of four.
- [Value roots](Ssz/Proofs/Codec/RootDomain.lean): every admissible value of a well-formed type has a 32-byte root, independently of serialization's offset limit.
- [Constructed branches](Ssz/Proofs/Codec/ProofCorrectness.lean): a branch built for any readable node reconstructs the value's root and passes verification, including across nested type boundaries.
- [Multiproofs](Ssz/Proofs/Merkle/Multiproof.lean): the computed helper frontier suffices for reconstruction, and proofs read from a finite tree rebuild its root.
  [Construction from values](Ssz/Proofs/Codec/MultiproofConstruction.lean) derives helper readability and reconstruction directly from successful value roots and claimed-node reads.
  No parent equations are required below leaves.
  [Multiproof size](Ssz/Proofs/Merkle/MultiproofSize.lean): the helper count and twice the claim count together come to the number of distinct claim ancestors plus two, which fixes the count exactly for any claim set at one depth.
  Claiming a whole level therefore needs no helpers, and claiming any `k` nodes of a level of depth `d` needs at most `k * (d - log2 k)`.
  A run of consecutive claims needs at least `d - log2 k`, so the shape of that bound cannot be improved.
- [Type paths](Ssz/Proofs/Codec/PathSelection.lean): recursive selections through present fields and elements agree with the value walker across every supported type family.
  Packed elements select their containing chunk, reserved steps select mixing words, and union descent follows the active option.
  A type-only index can name an absent position without asserting that a value is present; every readable padding node remains covered by the general branch theorem.
- [Authentication](Ssz/Proofs/Merkle/Authentication.lean): two accepted branches at the same index and root either open the same leaf or exhibit a SHA-256 collision between actual 64-byte branch inputs.
  [Multiproof binding](Ssz/Proofs/Merkle/MultiproofBinding.lean) gives the same guarantee for shared claims across different requests, with collision witnesses from the verifier's hash inputs.
- [Whole-value binding](Ssz/Proofs/Codec/Binding.lean): admissible values of the same well-formed type with equal roots are equal, or their Merkle computations contain distinct 64-byte inputs with equal SHA-256 hashes.
  [CommitmentSized](Ssz/Proofs/Codec/BindingDomain.lean) requires every nested variable collection count to fit its 256-bit mixing word.
  The proof recovers lengths, selectors, packed data, and nested values; callers supply no tree-alignment assumption.
- [Summaries](Ssz/Proofs/Codec/Summary.lean): replacing a field by a 32-byte array holding that field's own root leaves the struct root unchanged.
  A party holding only the summary computes the root a party holding the value computes, so a proof about anything inside the replaced value verifies against both.
- [The JSON mapping](Ssz/Proofs/Codec/JsonRoundTrip.lean): a document written for an admissible value of any well-formed type reads back as that value, at every shape of the universe.
  [Basic shapes](Ssz/Proofs/Codec/JsonLaws.lean) cover booleans, all six integer widths, the byte alias, both byte arrays, and all three bitfields.
  A bitfield is the hex of its own encoding, so its case is the codec round trip.
  [Hex](Ssz/Proofs/Codec/JsonHex.lean): a hex string the mapping wrote reads back as the bytes it came from.
  Objects: a name written into one is read back from it, and every name an object carries is one it was written from, so a written struct never trips the undeclared-field refusal.
  The mapping is deliberately not canonical, and a checked counterexample gives two documents for one value.
- [SHA-256](Ssz/Proofs/Hash/Sha256Spec.lean): the executable hash agrees with a separate mathematical model using 32-bit bitvectors, recursive message expansion, and the FIPS compression equations.
  The theorem covers byte messages shorter than 2^61 bytes, as required by the 64-bit bit-length field.
  [Published constants](Ssz/Proofs/Hash/Sha256Constants.lean): the eight chaining words and sixty-four round constants are checked against the square and cube roots of the first primes, rather than trusted as literals.

### The native implementation

- [Kernels](SszNative/Proofs/Kernel/Avx512/Main.lean): run on the model of the processor from their first instruction, the sixteen-lane kernel returns and writes each pair's SHA-256 digest where the caller asked.
  It changes no other memory and no register the calling convention keeps.
  The [SHA instruction kernel](SszNative/Proofs/Kernel/ShaNi/Main.lean) is proved the same way.
  The gathering kernels, [general](SszNative/Proofs/Kernel/Gather.lean) and [by width](SszNative/Proofs/Kernel/GatherNode.lean), copy each field into its slot and zero the rest.
- [References](SszNative/Proofs/Reference.lean): what each kernel writes is what the Lean body it stands in for computes, byte by byte.
- [Decoding checks](SszNative/Proofs/Validate/Main.lean): the check refuses exactly what deserialization refuses, with the same error, for every declaration.
- [Roots](SszNative/Proofs/Root/Main.lean): the root read from an encoding is the root of the value it decodes to, for every well-formed declaration.
  The buffer must be addressable: 64 times its size fits a machine word, which every array on a 64-bit machine satisfies.
- [Branches](SszNative/Proofs/Branch/Main.lean): nodes, branches, and multiproofs read from an encoding are the specification's, refusals included.
- [Compiled declarations](SszNative/Proofs/Schema/Main.lean): a declaration compiled once checks and roots values exactly as the declaration itself does.
- [Verification](SszNative/Proofs/Verify.lean): the native verifiers answer exactly what the specification's verifiers answer.

### Domains and limits

Composite serialization and deserialization both require fewer than 2^32 bytes at each composite level.
Primitive byte arrays have no offset table and therefore no such limit of their own.
A union adds its selector byte to the chosen option's encoding.
These distinctions are part of the mathematical size relation, rather than implicit machine-size assumptions.

Commitment binding has a separate length domain: variable collection counts must be below 2^256 at every nesting level.
`Fits` expresses value shape and declared capacities; `CommitmentSized` expresses exact length-word representability.
The low-level `lengthWord` keeps the low 256 bits outside that domain, so unrestricted root totality does not imply unrestricted binding.
SSZ does not separate roots by type; the whole-value theorem compares values under one declaration.
Its finite hash computation expands cached zero subtrees, preserving their mathematical hashes.

## Trust boundary

The proofs establish the stated properties of the formal definitions.
Agreement between those definitions and the English SSZ specification remains a review obligation.
The SHA-256 tables are derived: each constant is checked against the prime root FIPS 180-4 takes it from, so the model and the implementation cannot share a typo.
No theorem assumes SHA-256 is injective or collision-free.

The native implementation adds four trusted pieces.
The machine model in `SszNative/Asm/Semantics.lean` must describe what the processor does.
The regressions run every kernel, in every layout, on both the model and the processor, and compare.
The model leaves out faults and the direction flag, which the callers rule out, as its header says.
The printer and the assembler must turn each instruction list into the machine code the model reads.
The C bindings in `native/` must pick a kernel, split a count between the two hashing kernels, and check bounds, as their comments say.
The Lean compiler must run the tasks a wide tree is split into.

Kernel checking trusts Lean's kernel and standard logical foundations.
The axiom audit runs after the complete specification has been imported, so newly imported proof modules are included automatically.
The package is a foundation for a later implementation-refinement proof; such a proof must still relate that implementation's byte operations, errors, and resource limits to this model.
