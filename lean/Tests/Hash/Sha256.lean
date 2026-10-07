import Ssz.Hash.Sha256
import Lean

/-! Published SHA-256 examples and NIST byte-oriented validation vectors. -/

namespace Tests.Sha256

private def expect (label : String) (holds : Bool) : IO Unit := do
  -- Stop at the first disagreement with its vector or intermediate-step label.
  unless holds do throw (IO.userError label)

private def hex (text : String) : IO ByteArray := do
  -- Decode pairs strictly so malformed fixtures cannot silently become valid inputs.
  let mut bytes := ByteArray.empty
  let mut high : Option Nat := none
  for char in text.toList do
    let digit := char.toNat
    let value ← if digit ≥ 48 && digit ≤ 57 then pure (digit - 48)
      else if digit ≥ 97 && digit ≤ 102 then pure (digit - 87)
      else throw (IO.userError "invalid hexadecimal fixture")
    match high with
    | none => high := some value
    | some upper =>
      bytes := bytes.push (UInt8.ofNat (16 * upper + value))
      high := none
  unless high.isNone do throw (IO.userError "odd hexadecimal fixture length")
  return bytes

private def checkDigest (label : String) (message : ByteArray) (expected : String) : IO Unit := do
  -- Compare all 32 bytes against an independently published answer.
  let answer ← hex expected
  expect label (answer.size == 32 && Ssz.Sha256.hash message == answer)

private def knownAnswers (label text : String) (expectedCount : Nat) : IO Unit := do
  -- Response files encode bit lengths even for byte-oriented messages.
  let mut bits : Option Nat := none
  let mut message : Option ByteArray := none
  let mut count := 0
  for line in text.splitOn "\n" do
    if line.startsWith "Len = " then
      bits := (line.drop 6).toString.toNat?
    else if line.startsWith "Msg = " then
      message := some (← hex (line.drop 6).toString)
    else if line.startsWith "MD = " then
      let some length := bits | throw (IO.userError "missing fixture length")
      let some input := message | throw (IO.userError "missing fixture message")
      expect s!"{label}: byte-oriented length" (length % 8 == 0)
      -- NIST spells the zero-bit message as 00, which is a placeholder rather than a byte.
      let input := if length == 0 then ByteArray.empty else input
      expect s!"{label}: input length" (input.size == length / 8)
      checkDigest s!"{label}: {length} bits" input (line.drop 5).toString
      bits := none
      message := none
      count := count + 1
  -- Count every published answer so omitted cases fail the suite.
  expect s!"{label}: fixture count" (count == expectedCount && bits.isNone && message.isNone)

private def monteCarlo (text : String) : IO Unit := do
  -- SHAVS section 6.4 chains triples of digests for 1,000 iterations per answer.
  let mut seed := ByteArray.empty
  let mut count := 0
  for line in text.splitOn "\n" do
    if line.startsWith "Seed = " then
      seed ← hex (line.drop 7).toString
      expect "Monte Carlo seed width" (seed.size == 32)
    else if line.startsWith "COUNT = " then
      expect "Monte Carlo sequence" ((line.drop 8).toString.toNat? == some count)
    else if line.startsWith "MD = " then
      let mut a := seed
      let mut b := seed
      let mut c := seed
      for _ in [0:1000] do
        -- The oldest digest leaves the window after hashing the concatenated 96 bytes.
        let next := Ssz.Sha256.hash (a ++ b ++ c)
        a := b
        b := c
        c := next
      expect s!"Monte Carlo {count}" (c == (← hex (line.drop 5).toString))
      seed := c
      count := count + 1
  expect "Monte Carlo fixture count" (count == 100)

def run : IO Unit := do
  -- FIPS 180-2 appendix B covers one block, two blocks, and a million-byte message.
  checkDigest "FIPS abc" "abc".toUTF8
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
  checkDigest "FIPS two blocks"
    "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
  checkDigest "FIPS million a" ⟨Array.replicate 1000000 0x61⟩
    "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"

  -- NIST's worked abc example gives the first round and first expanded schedule word.
  let block := Ssz.Sha256.pad "abc".toUTF8
  expect "NIST abc schedule word 16" ((Ssz.Sha256.schedule block 0).toArray[16]! == 0x61626380)
  expect "NIST abc first round"
    ((Ssz.Sha256.round Ssz.Sha256.initialState Ssz.Sha256.roundConstants.toArray[0]! 0x61626380).toArray ==
      #[0x5d6aebcd, 0x6a09e667, 0xbb67ae85, 0x3c6ef372,
        0xfa2a4622, 0x510e527f, 0x9b05688c, 0x1f83d9ab])

  -- Embed the original response files so regression runs need no downloads or working directory.
  knownAnswers "NIST short" (include_str "SHA256ShortMsg.rsp") 65
  knownAnswers "NIST long" (include_str "SHA256LongMsg.rsp") 64
  monteCarlo (include_str "SHA256Monte.rsp")

end Tests.Sha256
