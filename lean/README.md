# Lean

The Lean specification of SSZ, and the proofs about it, live in [EthLib](https://github.com/ethereum/EthLib) as `EthLib.Consensus.Ssz`.
Its README says what it covers and what is proved.

This package checks that specification against this repository: the released test vectors, and the Python implementation on generated cases.
It also holds a native implementation of SSZ on x86-64 kernels, proved to compute the same roots, verdicts, and proofs as the specification.
It pins the EthLib commit it checks in `lakefile.toml`.

```text
SszNative     the native implementation, and its proofs
Conformance   readers for the released vectors and for the differential corpus
Tests         independent regression checks
Main.lean     the `conformance` executable
```

## The native implementation

SSZ also runs as x86-64 routines: serialization, the decoding check, roots, Merkle trees, nodes, branches, multiproofs, and their verification.

The routines are Lean data, so one definition is both what the proofs run and what the assembler file prints.
Kernels are lists of x86-64 instructions, which the proofs run on a model of the processor.
Drivers are programs in a small imperative language, turned into instructions by a compiler proved to keep their meaning.

```text
  EthLib.Consensus.Ssz       the specification, in EthLib
    │
    │  proved equal to
    ▼
  SszNative/Driver           drivers, in the small language       SszNative/Kernel   kernels, as x86-64 instructions
    │                                                                │
    │  SszNative/Ir/Compile  the proved compiler                    │
    ▼                                                                ▼
  SszNative/Asm/Machine      routines calling each other, run on the model of the processor
    │
    │  SszNative/Asm/Print   the printer
    ▼
  native/kernels_x86.S       the printed file, committed
    │
    ├──▶ native/bindings.c   Lean's own compiled code
    └──▶ src/ssz/native.py   Python, through ctypes
```

```text
SszNative/Asm        x86-64 instructions as data, their model, the whole machine, and the printer
SszNative/Ir         the small language, its meaning, its compiler, and linking
SszNative/Kernel     the kernels, feature detection, and the assembler file they print to
SszNative/Driver     the drivers: hashing, trees, the codec, the decoding check, roots, branches, and proofs
SszNative/Plan.lean  a type written as 64-bit words, which every driver walks
SszNative            the same operations as Lean functions over byte arrays, on the hashing kernels
SszNative/Proofs     the proofs that all of it computes the specification
native/              the printed routines, and the C bindings Lean's compiled code calls them through
```

### Kernels

Six kernels hash runs of node pairs with SHA-256:

| Kernel | Pairs per call | Instructions |
| --- | --- | --- |
| `Kernel/Avx512x2.lean` | 32, as two interleaved batches | AVX-512 |
| `Kernel/Avx512.lean` | 16 | AVX-512 |
| `Kernel/ShaNiDual.lean` | 2, interleaved | SHA, SSSE3, SSE4.1 |
| `Kernel/ShaNi.lean` | 1 | SHA, SSSE3, SSE4.1 |
| `Kernel/Avx2.lean` | 8 | AVX2 |
| `Kernel/Baseline.lean` | 4 | SSE2, which every x86-64 processor has |

Each is printed three times: for adjacent pairs, for two columns, and for a column against one fixed node.

The gathering kernels copy fields out of fixed-width records into zero-padded nodes.
One is a general byte copy, and the others are AVX routines for common widths.

`Kernel/Detect.lean` asks the processor what it supports, with cpuid and xgetbv, and answers a mask of the usable kernel families.

### Drivers

A driver receives a type as the address of its plan, the words `Plan.lean` writes, and reads the encoding in place.
It never builds the value an encoding holds.

The hashing driver cuts a run of pairs across the fastest kernels the mask allows, down to the SSE2 one.
Every other driver hashes through it, so every call is answered on every x86-64 processor.

Each driver mirrors one Lean function of `SszNative`, step for step, and is proved to compute it.
That Lean function is proved, in turn, to compute the specification.

### Two consumers

Lean's compiled code calls the hashing and gathering routines through `native/bindings.c`.
The bindings only marshal arrays and check ranges; detection and dispatch run in the printed routines.

Python calls the routines directly through ctypes, when its native backend is on.
It uses the decoding check, roots, merkleization, hashing, the incremental trees, and verification.
The codec and proof-construction drivers are proved, but Python does not call them yet.

### Build, regenerate, and check

`native/kernels_x86.S` is committed, so building needs no extra step.

```bash
cd lean
lake build                                  # check every proof, then assemble and link the routines
lake env lean --run scripts/kernels.lean    # print native/kernels_x86.S again from the Lean data
lake exe regressions                        # run the kernels on this processor and on the model
```

`just lean-kernels` builds the assembly module and runs the printer.
The regressions fail when the committed file differs from what the Lean data prints.
`just test-native` runs the Python suite on the routines, and fails where they cannot run.

### What the native routines assume

`Native.validate` checks encoding bytes exactly as deserialization does; it does not check
that the descriptor itself is a legal SSZ declaration. Native roots, nodes and proof
construction assume a successful `Desc.wellFormed` check. The native root/proof
reference-equivalence theorems also require `64 * bytes.size + 128 < USize.size`.
These premises are not memory-allocation or runtime bounds.

`Checked.compile` checks a declaration once and compiles it, or returns why it is illegal.
Its roots agree with the specification under the buffer premise alone.
`Schema.compile` skips the legality check, so its roots need a separately checked declaration.
A schema's cache is always the one its declaration compiles to: the type carries that equation.

## Build and test

Generate the local fixtures with `just fill` before running conformance tests.

```bash
just lean          # build the conformance and regression executables
just lean-test     # run the released vectors and the independent Lean regressions
just lean-parity   # compare generated cases with the Python implementation
just lean-kernels  # print the native kernels from their Lean programs
just lean-bench    # time the native implementation on beacon-chain workloads
```

The toolchain is pinned in `lean-toolchain`, and must match EthLib's.
Warnings in this package are errors.

The released vectors check all six of the formats `fixtures/` carries: byte encodings and their
roots, illegal declarations, generalized indices, JSON documents, single branches, and multiproofs.
Each vector carries its own declaration, so no registry of named types is kept on this side.
The run is held to the case count the release declares, so a vector the walk never reached fails
the run rather than leaving a passing count behind.
The fixture directory must contain a readable JSON manifest with a positive integer `caseCount`;
missing or malformed metadata and empty releases fail the run.
Differential tests additionally compare defaults, compatibility, paths, branches, and multiproofs
on types neither implementation was written for.
They also damage each encoding, and require the refusal Python names, or the same acceptance.
Their corpus must be an object containing only `cases` and/or `compatible` arrays, with at least
one entry in total. Either section may be omitted, but a present section of the wrong kind fails.
These vectors are generated by this repository's Python implementation; agreement is not an
independent proof of conformance.
The Lean regressions add independent SHA-256 answers, deep-tree checks, malformed inputs,
and exhaustive canonical re-encoding checks for one- and two-byte inputs across twelve small types.

## Proven properties of the native implementation

### The native routines in Lean

- [Kernels](SszNative/Proofs/Kernel/Avx512/Main.lean): run on the model of the processor from their first instruction, the sixteen-lane kernel returns and writes each pair's SHA-256 digest where the caller asked.
  It changes no other memory and no register the calling convention keeps.
  The other five hashing kernels are proved the same way, each by a `program_correct` in its own `Main.lean`: [AVX-512, two batches](SszNative/Proofs/Kernel/Avx512x2/Main.lean), [SHA](SszNative/Proofs/Kernel/ShaNi/Main.lean), [SHA, two pairs](SszNative/Proofs/Kernel/ShaNiDual/Main.lean), [AVX2](SszNative/Proofs/Kernel/Avx2/Main.lean), and [SSE2](SszNative/Proofs/Kernel/Baseline/Main.lean).
  The gathering kernels, [general](SszNative/Proofs/Kernel/Gather.lean) and [by width](SszNative/Proofs/Kernel/GatherNode.lean), copy each field into its slot and zero the rest.
- [References](SszNative/Proofs/Reference.lean): what each kernel writes is what the Lean body it stands in for computes, byte by byte.
- [Decoding checks](SszNative/Proofs/Validate/Main.lean): the check refuses exactly what deserialization refuses, with the same error, for every declaration.
- [Roots](SszNative/Proofs/Root/Main.lean): the root read from an encoding is the root of the value it decodes to, for every well-formed declaration.
  The exact buffer premise is `64 * bytes.size + 128 < USize.size`; it is supplied by the caller.
- [Branches](SszNative/Proofs/Branch/Main.lean): nodes, branches, and multiproofs read from an encoding are the specification's, refusals included, for a well-formed descriptor and the same buffer premise as roots.
- [Compiled declarations](SszNative/Proofs/Schema/Main.lean): every schema checks encodings exactly as its declaration does, legal or not.
  Its roots are the specification's for a well-formed declaration and the same buffer premise as roots.
  A checked schema carries that legality, and the checked factory refuses exactly the illegal declarations.
- [Verification](SszNative/Proofs/Verify.lean): the native verifiers answer exactly what the specification's verifiers answer.

### The compiled routines

These theorems speak of the routines Python calls.
Each states what a call returns and writes, and which memory it leaves alone, under the ranges and stack room it names.

- [The compiler](SszNative/Proofs/Ir/Fn.lean): `module_ok` says every call to a compiled function computes the function's meaning in the small language, given that the routines outside the language keep their contracts.
  `compileFn_runs` says compiled code needs no instruction set extension.
  [`placed_of_linkCheck`](SszNative/Proofs/Ir/Link.lean) says an image that passes the link check holds each function where the proof looks for it.
- [The shipped image](SszNative/Proofs/Shipped.lean): `shipped_linkCheck` says the printed image passes the link check, and `shipped_ok` says every call to it computes its meaning.
  `shipped_hashTreeRoot`, `shipped_validate`, `shipped_checkPlan`, the three tree store theorems, `shipped_verifyBranch`, `shipped_verifyMultiproof`, `shipped_proveNode`, `shipped_proveBranch`, `shipped_proveMultiproof` and `shipped_proveScratch` state the top theorems on that image's whole machine.
- [Detection](SszNative/Proofs/Kernel/Detect.lean): `featureMask_bits` says each bit of the mask implies the features its kernel family needs, and `runs_baseline` says the SSE2 kernel runs on every processor.
- [Kernel contracts](SszNative/Proofs/Ir/Kernels.lean): `hash_leafOk` and `hashFrame_leafOk` turn each kernel's `program_correct` into the call contract the drivers rely on.
- [Hashing](SszNative/Proofs/Driver/Hash.lean): `hashCalls` says the hashing driver hashes the whole run, whichever kernels the mask allows, over the six hashing kernels and their three layouts.
- [Merkleization](SszNative/Proofs/Driver/Tree.lean): `treeCalls` says `ssz_merkleize` writes the root of the perfect tree over the nodes, padded with zero subtrees.
  `hashingOk` packages hashing and merkleization as `HashingOk`, which the later theorems take.
- [Gathering](SszNative/Proofs/Driver/Gather.lean): `gatherCalls` says the gathering driver copies every field into its slot, on whichever routine its width has.
- [The decoding check](SszNative/Proofs/Driver/Validate/Main.lean): `validate_correct` says `ssz_validate` returns zero exactly when the Lean check accepts, and one with the refusal's four words when it refuses.
  [`validate_calls_named`](SszNative/Proofs/Plan/Rename.lean) lifts the requirement that fields be named by position.
- [The plan check](SszNative/Proofs/Driver/Validate/PlanSound.lean): `checkPlan_iff` says `ssz_check_plan` returns zero exactly when the bytes are the plan of a legal type within the native limits.
  So the premises of the theorems above are checked at run time, not trusted.
- [Roots](SszNative/Proofs/Driver/Root/Top.lean): `hashTreeRoot_calls` says `ssz_hash_tree_root` writes the specification's root of the value an accepted encoding holds.
  It rests on `rootOf_ok`, proved for every type by induction, and on [`rootsOf_ok`](SszNative/Proofs/Driver/Root/Dispatch.lean) for the fixed-size roots driver.
- [The codec](SszNative/Proofs/Driver/Serialize.lean): `ssz_assemble_correct` says `ssz_assemble` lays the parts out as serialization does, refusals included.
  [`ranges_ok`](SszNative/Proofs/Driver/Ranges.lean) says `ssz_ranges` cuts a composite where deserialization cuts it.
- Verification: [`verify_branch_hashing`](SszNative/Proofs/Driver/Branch/Bridge.lean) and [`verify_multiproof_hashing`](SszNative/Proofs/Driver/Branch/VerifyMultiproof.lean) say the compiled verifiers answer what the Lean verifiers answer.
- Construction: [`prove_node_ok`, `prove_branch_ok` and `prove_multiproof_ok`](SszNative/Proofs/Driver/Prove/Entry.lean) say the builders answer what the Lean node, branch and multiproof answer, and write their nodes.
  They hold for an encoding validation accepts, a type nesting at most 64 deep, and the scratch [`prove_scratch_calls`](SszNative/Proofs/Driver/Prove/Scratch.lean) computes.
  The walk to one node rests on [`node_at_ok`](SszNative/Proofs/Driver/Prove/NodeAt.lean), proved for every type by induction on its nesting.
- [Incremental trees](SszNative/Proofs/Driver/TreeStore.lean): `treeBuild_calls` builds the whole tree over the leaves.
  `treeUpdate_calls` rehashes only the paths above rewritten leaves and leaves the whole tree over the new leaves.
  `treeRoot_calls` writes the specification's root at the declared depth, with a word mixed in when one is given.

## Trust boundary of the native implementation

The native implementation proves its kernels against a model of the processor, not the processor itself.

Everything between that model and a running client is trusted.

The ledger below lists each such boundary, what stands in for a proof, and the evidence class:

- **proof**: checked by Lean's kernel.
- **test**: a finite regression run.
- **review**: read by a person.
- **open**: no evidence yet.

| | Boundary | What is trusted | Evidence |
|---|---|---|---|
| T1 | Instruction semantics | `SszNative/Asm/Semantics.lean` follows Intel's manual, instruction by instruction; [Intel references](#intel-references) lists the pages. It leaves out faults, the direction flag, memory mapping, and the sign, overflow, parity and adjust flags. A flag the manual leaves undefined is `undefinedFlag`, an opaque function, so no proof can rely on its value. | review, test |
| T2 | The processor's answers | `Cpu` gives any answer to cpuid and xgetbv, and the proofs hold for every answer. What is trusted is that the bits `Cpu.has` in `SszNative/Asm/Machine.lean` reads mean the feature runs, as the manual's volume 1, sections 13.2 and 15.2, say. | review, test |
| T3 | Printer, assembler, and linker | Each line `SszNative/Asm/Print.lean` prints assembles to the modeled instruction, and the linker and loader place the routines and the 64-byte-aligned table. `routines_valid` proves every operand fits its encoding, and `routines_distinct` that no two routines share a name. The encoding itself is not decoded back. | proof (operands, names), test (freshness, hardware) |
| T4 | The printed image | The list `SszNative/Kernel/Assembly.lean` prints is the image `Module.link` builds from the shipped drivers and kernels. [`shipped_linkCheck`](SszNative/Proofs/Shipped.lean) proves it passes `linkCheck`, and the `shipped_` theorems there run each exported routine to its return on that image. What remains trusted is that the printed file is assembled and loaded as that image, under T3. | proof |
| T5 | The calling convention at the boundary | The routines are proved to keep the System V convention on the model: arguments in rdi to r9, the result in rax, the kept registers and the stack pointer restored. What is trusted is that the caller, ctypes or C, calls them that way, with the direction flag clear and the stack room each theorem's premise names. | review, test |
| T6 | C bindings | `native/bindings.c` turns Lean arrays into pointers, checks every range, and falls back to the Lean body where a range runs past its array. Gather falls back before its source cursor could leave the proved address range. Axiom audits cannot see C. | review, test |
| T7 | Python glue | `src/ssz/native.py` writes the plan of a Python type and sizes every buffer. `kept.py` decides which nodes are stale after a mutation, `stored.py` builds values over an accepted encoding, and `lazy.py` decodes each element on first read. The plan check proves a plan is legal, not that it is the plan of the Python type it came from. | test |
| T8 | Contracts the top theorems take | `HashingOk`, `GatherModule` and the walk's `NodeAtOk` are discharged, from the module's shape by `hashingOk`, `hashingOk_append` and `gatherModule_append`, and for the walk by `nodeAtOk_of`. | proof |
| T9 | Reference correspondence | The Lean reference matches the Python specification, including refusals. | test (conformance, differential) |
| T10 | Compiler and runtime | Lean compiles byte operations and parallel tasks faithfully. Allocation, stack depth, timing and constant-time behavior are not proved. | test |
| T11 | Hardware coverage | Each kernel runs on the processors it claims. The regressions report the paths they actually ran; `SSZ_REQUIRE_AVX512=1` fails a run without AVX-512. | test, on the host's processor only |
| T12 | Client integration | A production client uses fork-correct schemas and realistic workloads. The benchmarks are subsets. | open |
| T13 | Collision resistance | The collision-witness theorems are structural: a forgery yields two different preimages of one hash. They are not a probabilistic security game with an efficient reduction. | proof (structural only) |

### Axioms

`audit_native`, run at the end of `SszNative/Proofs.lean`, checks every declaration under `EthLib.Consensus.Ssz.Native`.
Each may depend only on `propext`, `Classical.choice` and `Quot.sound`.
EthLib's `lake exe check-decls` holds the specification to the same three.

`native_decide` and `bv_decide` would add `Lean.ofReduceBool`, which the audit rejects, and neither appears in the sources.
The large finite checks, `routines_valid` and `routines_distinct`, use `decide +kernel`, which Lean's kernel evaluates itself.

### How the tests cover the model gap

`Tests/Native.lean` runs on the host processor as part of `lake exe regressions`.

It restricts the detected mask to each of `15, 7, 6, 5, 4, 8, 0`, so each kernel family runs alone, together with the others, and not at all.
Under each mask, every layout is compared with its Lean reference at counts around every batch size and at misaligned offsets.
Coverage counters in the bindings then assert that the dispatcher, the fallback, and the range refusal each ran.

The same test runs each kernel on the model and compares the bytes with what the processor wrote.
A disagreement there points at the model rather than at the kernel.

It also checks the operand bounds at their edges, and that the committed assembler file is the printed one.

A mask can only take features away, so a kernel the host lacks is tested on the model alone.

On the Python side, `just test-native` runs the whole suite on the routines, and `just test-cov-gate` holds it to full coverage with the backend on.

### Intel references

The model follows the [Intel 64 and IA-32 Architectures Software Developer's Manual](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html).
Volume 2A covers instructions A to L, 2B covers M to U, 2C covers V, and 2D covers W to Z.
Each row names the mnemonics; the manual files each under the instruction page whose title lists it, and the [vector pages](https://intel.github.io/SDM/category/vector.html) use the same titles.

| Family | Model constructors | Manual page | Volume |
|---|---|---|---|
| Integer arithmetic | `addImm`, `addReg`, `subImm`, `alu` | ADD, SUB, AND, OR, XOR, IMUL | 2A, 2B, 2D |
| Compares and tests | `cmp`, `cmpImm`, `test` | CMP, TEST | 2A, 2B |
| Shifts | `shlImm`, `shrImm` | SAL/SAR/SHL/SHR | 2B |
| Division | `div` | DIV | 2A |
| Moves and loads | `movReg`, `movImm`, `load`, `store`, `loadByte`, `loadWord`, `zeroReg` | MOV, MOVZX, XOR | 2B, 2D |
| String copies | `repMovsb`, `repStosb` | REP prefix, MOVS/MOVSB, STOS/STOSB | 2B |
| Control flow | `jz`, `jnz`, `jcc`, `jmp`, `call`, `ret` | Jcc, JMP, CALL, RET | 2A, 2B |
| Stack | `push`, `pop` | PUSH, POP | 2B |
| Byte swap | `bswap` | BSWAP | 2A |
| Feature detection | `cpuid`, `xgetbv` | CPUID, XGETBV, and volume 1, sections 13.2 and 15.2, as `SszNative/Asm/Machine.lean` cites them | 2A, 2D, 1 |
| SSE2 | `movdqu`, `movdquStore`, `movdqa`, `paddd`, `padddMem`, `pxor`, `pand`, `pandn`, `psrld`, `pslld`, `pshufd` | MOVDQU, MOVDQA, PADDD, PXOR, PAND, PANDN, PSRLD, PSLLD, PSHUFD | 2B |
| SSSE3 and SSE4.1 | `pshufb`, `palignr`, `pblendw` | PSHUFB, PALIGNR, PBLENDW | 2B |
| SHA | `sha256rnds2`, `sha256msg1`, `sha256msg2` | SHA256RNDS2, SHA256MSG1, SHA256MSG2 | 2B |
| AVX moves | `vfromGpr`, `vload4`, `vload8`, `vload16`, `vloadHalf`, `vstoreHalf`, `ymov`, `vzeroupper` | MOVD/MOVQ, MOVQ, MOVDQU, MOVDQA, VZEROUPPER | 2B, 2C |
| AVX2 | `yadd`, `yaddMem`, `yxor`, `yand`, `yandn`, `yor`, `yshr`, `yshl`, `yshufb`, `yunpackLo32`, `yunpackHi32`, `yunpackLo64`, `yunpackHi64`, `yperm128` | PADDD, PXOR, PAND, PANDN, POR, PSRLD, PSLLD, PSHUFB, PUNPCKLDQ, PUNPCKHDQ, PUNPCKLQDQ, PUNPCKHQDQ, VPERM2I128 | 2B, 2C |
| AVX-512 | `vload`, `vstore`, `vmov`, `vinsertHigh`, `vadd`, `vaddMem`, `vshr`, `vshufb`, `vshufps` | MOVDQU (VMOVDQU32), MOVDQA (VMOVDQA32), VINSERTI64x4, PADDD, PSRLD, PSHUFB, SHUFPS | 2B, 2C |
| AVX-512 rotates and logic | `vror`, `vternlog` | PRORD (VPRORD), VPTERNLOGD | 2B, 2C |
| AVX-512 permutes | `vpermi2d`, `vpermi2q` | VPERMI2D, VPERMI2Q | 2C |
