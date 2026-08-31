# ssz-testing

Generation of SSZ conformance test vectors for the `eth-ssz-specs` reference
implementation.

The package drives the spec's own encode / decode / `hash_tree_root` logic over a
curated set of values and emits language-neutral JSON vectors. Other SSZ
implementations replay these vectors to check byte-for-byte and root-for-root
agreement.

## Running

From the workspace root:

```bash
just fill                                   # generate every vector into fixtures/
uv run --group test fill --clean            # same thing, without just
uv run --group test fill tests/fillers/ssz  # fill a single directory
uv run --group test fill --collect-only     # preview, writing and removing nothing
```

The package's own tests run with the rest of the suite, from the workspace root:

```bash
uv run --group test pytest packages/testing/tests
```

The fillers themselves live in the main repository under `tests/fillers/`. They are
plain pytest functions that receive an `ssz_test` fixture and describe one value each.

## Output

Vectors are written under `fixtures/<format>/<test-path>/<function>.json`. Every entry
carries:

- `typeName` — the SSZ type under test.
- `serialized` — the 0x-prefixed SSZ bytes.
- `root` — the 0x-prefixed `hash_tree_root` (empty for decode-failure vectors).
- `_info` — provenance metadata, including a content `hash`.

Decode-failure vectors additionally carry `rawBytes` (the rejected input) and a
`rejectionReason`, the name of the `ValueFault` the decoder raised.

`--output` names a directory inside the workspace, and `--clean` removes it in full, so a
path the workspace does not contain is refused rather than deleted.

## Layout

```
src/ssz_testing/
  __init__.py          # public exports (SSZTest, SSZFixture, SSZTestFiller, ...)
  fixtures.py          # fixture formats: input specs and emitted vectors
  hex_codec.py         # 0x-prefixed hex helpers
  plugin.py            # pytest plugin: collection, generation, writing
  cli.py               # the `fill` command
  pytest_ini_files/    # pytest config used by the fill command
tests/                 # the package's own tests
```
