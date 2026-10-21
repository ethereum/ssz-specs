import SszNative

/-!
Timing the native implementation on beacon-chain workloads: `lake exe bench`.

Each workload prints its root, so other implementations fed the same data can be checked against it.
-/

open Ssz Ssz.Native

/-- Little-endian bytes of a word, appended. -/
def pushWord (b : ByteArray) (x : Nat) (width : Nat) : ByteArray :=
  (List.range width).foldl (fun b k => b.push (UInt8.ofNat (x >>> (8 * k)))) b

/-- Bytes from a seed: byte k is the seed plus k, wrapping. -/
def pushRun (b : ByteArray) (seed count : Nat) : ByteArray :=
  (List.range count).foldl (fun b k => b.push (UInt8.ofNat (seed + k))) b

/-- A validator record, as the beacon chain declares it. -/
def validator : Desc :=
  .container
    ["pubkey", "withdrawal_credentials", "effective_balance", "slashed", "activation_eligibility_epoch",
      "activation_epoch", "exit_epoch", "withdrawable_epoch"]
    [.byteVector 48, .byteVector 32, .uint 8, .bool, .uint 8, .uint 8, .uint 8, .uint 8]

/-- The encoding of validator i, with the fields every implementation under comparison is fed. -/
def pushValidator (b : ByteArray) (i : Nat) : ByteArray :=
  let max := 2 ^ 64 - 1
  let b := pushRun b i 48
  let b := pushRun b (3 * i) 32
  let b := pushWord b (32000000000 + i) 8
  let b := b.push (if i % 7 == 0 then 1 else 0)
  let b := pushWord b i 8
  let b := pushWord b (i + 1) 8
  let b := pushWord b max 8
  pushWord b (max - i) 8

/-- The beacon state's heaviest fields: roots, validators, balances, participation, and scores. -/
def state : Desc :=
  let roots (n : Nat) := Desc.vector (.byteVector 32) n
  let counted (d : Desc) := Desc.list d (2 ^ 40)
  .container
    ["genesis_time", "slot", "fork", "block_roots", "state_roots", "validators", "balances", "randao_mixes",
      "previous_epoch_participation", "current_epoch_participation", "inactivity_scores"]
    [.uint 8, .uint 8,
      .container ["previous_version", "current_version", "epoch"] [.byteVector 4, .byteVector 4, .uint 8],
      roots 8192, roots 8192, counted validator, counted (.uint 8), roots 65536, counted (.uint 1), counted (.uint 1),
      counted (.uint 8)]

/-- Root i of the state's root vectors: byte k is five times i plus k, wrapping. -/
def pushRoot (b : ByteArray) (i : Nat) : ByteArray :=
  pushRun b (5 * i) 32

/-- The encoding of a state with a count of validators, as every implementation under comparison is fed. -/
def stateBytes (count : Nat) : ByteArray :=
  let validators := (List.range count).foldl pushValidator (ByteArray.emptyWithCapacity (121 * count))
  let balances := (List.range count).foldl (fun b i => pushWord b (32000000000 + i) 8) .empty
  let previous := (List.range count).foldl (fun b i => b.push (UInt8.ofNat (i % 8))) .empty
  let current := (List.range count).foldl (fun b i => b.push (UInt8.ofNat (i % 5))) .empty
  let scores := (List.range count).foldl (fun b i => pushWord b (i % 3) 8) .empty
  -- The fixed part: two integers, the fork, two root vectors, an offset, an offset, the mixes, three offsets.
  let fixedSize := 8 + 8 + 16 + 2 * 32 * 8192 + 4 + 4 + 32 * 65536 + 4 + 4 + 4
  let offsets := [validators, balances, previous, current].foldl
    (fun (acc : List Nat × Nat) part => (acc.1 ++ [acc.2], acc.2 + part.size)) ([], fixedSize)
  let at_ (k : Nat) := offsets.1.getD k 0
  let b := pushWord (pushWord (ByteArray.emptyWithCapacity (fixedSize + 141000000)) 1606824023 8) 9000000 8
  let b := pushWord (pushRun (pushRun b 3 1 |>.push 0 |>.push 0 |>.push 0) 4 1 |>.push 0 |>.push 0 |>.push 0) 269568 8
  let b := (List.range 8192).foldl pushRoot b
  let b := (List.range 8192).foldl (fun b i => pushRoot b (i + 9000)) b
  let b := pushWord (pushWord b (at_ 0) 4) (at_ 1) 4
  let b := (List.range 65536).foldl (fun b i => pushRoot b (i + 20000)) b
  let b := pushWord (pushWord (pushWord b (at_ 2) 4) (at_ 3) 4) offsets.2 4
  b ++ validators ++ balances ++ previous ++ current ++ scores

/-- The median and the spread of a run of timings, after a warm-up. -/
def time (label : String) (input : IO.Ref ByteArray) (work : ByteArray → ByteArray) : IO Unit := do
  -- Warm the caches, the allocator, and the clock for a third of a second.
  let warm ← IO.monoNanosNow
  while (← IO.monoNanosNow) - warm < 300000000 do
    let r := work (← input.get)
    if r.size == 1 then IO.println "?"
  let mut samples : Array Nat := #[]
  for _ in [0:31] do
    let b ← input.get
    let t0 ← IO.monoNanosNow
    let r := work b
    -- Reading the result keeps the work from being skipped.
    if r.size == 1 then IO.println "?"
    let t1 ← IO.monoNanosNow
    samples := samples.push (t1 - t0)
  let s := samples.qsort (· < ·)
  -- Nanoseconds below ten microseconds, microseconds above.
  let fmt (n : Nat) : String :=
    if n < 10000 then s!"{n} ns" else s!"{n / 1000}.{n / 100 % 10} us"
  IO.println s!"{label}: median {fmt s[15]!}, p10 {fmt s[3]!}, p90 {fmt s[27]!}"

/-- A root in hex. -/
def hex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let d := Nat.toDigits 16 x.toNat
    String.ofList (if d.length < 2 then '0' :: d else d))

/-- The root, or the empty buffer for a refused encoding. -/
def rooted (d : Desc) (b : ByteArray) : ByteArray :=
  (hashTreeRoot d b).toOption.getD ByteArray.empty

def main : IO Unit := do
  let limit := 2 ^ 40
  -- A list of a hundred thousand integers.
  let ints := List.range 100000 |>.foldl (fun b i => pushWord b i 8) (ByteArray.emptyWithCapacity 800000)
  let intList := Desc.list (.uint 8) limit
  IO.println s!"ints root {hex (rooted intList ints)}"
  time "List[uint64] 100k root" (← IO.mkRef ints) (rooted intList)
  -- One block header.
  let header := pushRun (pushRun (pushRun (pushWord (pushWord ByteArray.empty 7 8) 9 8) 5 32) 10 32) 15 32
  let headerType := Desc.container ["slot", "proposer_index", "parent_root", "state_root", "body_root"]
    [.uint 8, .uint 8, .byteVector 32, .byteVector 32, .byteVector 32]
  IO.println s!"header root {hex (rooted headerType header)}"
  time "BeaconBlockHeader root" (← IO.mkRef header) (rooted headerType)
  -- The same header against its declaration compiled once.
  let headerSchema := Schema.compile headerType
  time "BeaconBlockHeader root, compiled" (← IO.mkRef header) fun b =>
    (headerSchema.hashTreeRoot b).toOption.getD ByteArray.empty
  -- A million validators, as in a beacon state.
  let count := 1000000
  let validators := (List.range count).foldl pushValidator (ByteArray.emptyWithCapacity (121 * count))
  let validatorList := Desc.list validator limit
  IO.println s!"validators root {hex (rooted validatorList validators)}"
  let input ← IO.mkRef validators
  time "List[Validator] 1M root" input (rooted validatorList)
  time "List[Validator] 1M decoding check" input fun b =>
    if (validate validatorList b).isOk then zeroNode else ByteArray.empty
  -- A beacon state with the same million validators.
  let stateEncoding := stateBytes count
  IO.println s!"state root {hex (rooted state stateEncoding)}"
  time "BeaconState-like 1M root" (← IO.mkRef stateEncoding) (rooted state)
  -- The branch for one validator's public key: element 123456 of the list's contents, then field 0.
  let index := (2 ^ 41 + 123456) * 8
  let branch := (buildProof validatorList validators index).toOption.getD []
  let leaf := (nodeRoot validatorList validators index).toOption.getD ByteArray.empty
  let root := rooted validatorList validators
  let verified := (verifyMerkleProof leaf branch index root).toOption == some true
  IO.println s!"branch of {branch.length} nodes, verified {verified}"
  time "List[Validator] 1M branch" input fun b =>
    if (buildProof validatorList b index).isOk then zeroNode else ByteArray.empty
  time "List[Validator] 1M branch verification" (← IO.mkRef leaf) fun leaf =>
    if (verifyMerkleProof leaf branch index root).toOption == some true then zeroNode
    else ByteArray.empty
