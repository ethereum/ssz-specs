import SszNative.Driver.Hash
import SszNative.Ir.Wf

/-!
Verifying a branch or a multiproof against a root, on the hashing kernels.

A generalized index is one 64-bit word, so a tree deeper than 63 levels cannot be named.
Every node is 32 bytes, so the width checks the Lean verifiers make always pass here.

Each verifier answers one word:

```text
    0    the nodes rebuild a different root
    1    the nodes rebuild the expected root
    2    the processor has no hashing kernel
    3    an index of zero, which names no node
    4    the index of the root, which has no branch
    5    a branch whose length is not the depth of its index
    6    leaves that do not pair one to one with the indices
    7    a proof whose node count is not the number of helper indices
    8    a request naming no index
    9    one index named twice
    10   an index below another of the same request
    11   a proof from which no root can be rebuilt
```

A multiproof's node sets are lists of 40-byte entries: an index, then its node.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt

/-- The bytes of one entry of a node set: an 8-byte index, then a 32-byte node. -/
abbrev entryBytes : Nat := 40

namespace Level
/-- The index, halved until it is one. -/
abbrev x : Var := ⟨0⟩
/-- The levels counted so far. -/
abbrev d : Var := ⟨1⟩

/-- The level of an index below the root, the position of its leading bit: argument x. -/
def fn : Fn :=
  { params := 1, vars := 2, result := d,
    body := .block [d ::= 0, while_ (lt 1 x) [x ::= .shr x 1, d ::= d + 1]] }
end Level

namespace Find
/-- The address of the first word searched. -/
abbrev base : Var := ⟨0⟩
/-- The distance between two searched words. -/
abbrev stride : Var := ⟨1⟩
/-- How many words are searched. -/
abbrev count : Var := ⟨2⟩
/-- The word searched for. -/
abbrev key : Var := ⟨3⟩
/-- The position being read. -/
abbrev i : Var := ⟨4⟩
/-- Where the search stops: the count, or the first match. -/
abbrev stop : Var := ⟨5⟩

/--
The position of the first of a count of words, a stride apart, equal to a key: arguments base, stride, count, key.

Returns the count when no word matches.
-/
def fn : Fn :=
  { params := 4, vars := 6, result := i,
    body := .block [i ::= 0, stop ::= count,
      while_ (lt i stop) [ifElse (eq (ld (base + stride * i)) key) [stop ::= i] [i ::= i + 1]]] }
end Find

namespace Same
/-- The address of one node. -/
abbrev a : Var := ⟨0⟩
/-- The address of the other node. -/
abbrev b : Var := ⟨1⟩
/-- The byte being compared. -/
abbrev i : Var := ⟨2⟩
/-- One while every byte so far agrees. -/
abbrev same : Var := ⟨3⟩

/-- One when two 32-byte nodes agree byte for byte, and zero otherwise: arguments a, b. -/
def fn : Fn :=
  { params := 2, vars := 4, result := same,
    body := .block [same ::= 1, i ::= 0,
      while_ (lt i 32) [when (ne (ld1 (a + i)) (ld1 (b + i))) [same ::= 0], i ::= i + 1]] }
end Same

namespace VerifyBranch
/-- The job the caller filled. -/
abbrev job : Var := ⟨0⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨1⟩
/-- The address of the leaf. -/
abbrev leaf : Var := ⟨2⟩
/-- The address of the first branch node. -/
abbrev proof : Var := ⟨3⟩
/-- How many branch nodes there are. -/
abbrev count : Var := ⟨4⟩
/-- The generalized index of the leaf. -/
abbrev index : Var := ⟨5⟩
/-- The address of the expected root. -/
abbrev root : Var := ⟨6⟩
/-- The 64-byte scratch area, two nodes used in turn. -/
abbrev scratch : Var := ⟨7⟩
/-- The depth of the index. -/
abbrev depth : Var := ⟨8⟩
/-- The index's turns not yet climbed, lowest first. -/
abbrev turns : Var := ⟨9⟩
/-- The address of the node climbed so far. -/
abbrev cur : Var := ⟨10⟩
/-- Where the next parent goes. -/
abbrev out : Var := ⟨11⟩
/-- The levels climbed so far. -/
abbrev level : Var := ⟨12⟩
/-- A hashing call's result. -/
abbrev got : Var := ⟨13⟩
/-- Zero unless some hashing call found no kernel. -/
abbrev status : Var := ⟨14⟩
/-- The answer. -/
abbrev answer : Var := ⟨15⟩

/--
Whether one leaf and its branch rebuild a root: arguments job, ctx.

The job holds six words:

```text
    job + 0    the address of the leaf
    job + 8    the address of the branch, 32 bytes per node, from the leaf upward
    job + 16   the number of branch nodes
    job + 24   the generalized index of the leaf
    job + 32   the address of the expected root
    job + 40   the address of a 64-byte scratch area, apart from everything else
```
-/
def fn : Fn :=
  { params := 2, vars := 16, result := answer,
    body := .block [leaf ::= ld job, proof ::= ld (job + 8), count ::= ld (job + 16), index ::= ld (job + 24),
      root ::= ld (job + 32), scratch ::= ld (job + 40),
      ifElse (eq index 0) [answer ::= 3]
        [ifElse (eq index 1) [answer ::= 4]
          [callInto depth "ssz_branch_level" [index],
            ifElse (ne depth count) [answer ::= 5]
              [cur ::= leaf, turns ::= index, level ::= 0, status ::= 0,
                while_ (lt level count) [
                  -- The parent goes to the scratch node the current one is not in.
                  out ::= scratch + 32 * (level &&& 1),
                  -- A set bit puts the current node on the right.
                  ifElse (ne (turns &&& 1) 0)
                    [callInto got "ssz_hash_columns" [out, proof + 32 * level, cur, 1, ctx]]
                    [callInto got "ssz_hash_columns" [out, cur, proof + 32 * level, 1, ctx]],
                  status ::= status ||| got, cur ::= out, turns ::= .shr turns 1, level ::= level + 1],
                ifElse (ne status 0) [answer ::= 2] [callInto answer "ssz_branch_same" [cur, root]]]]]] }
end VerifyBranch

namespace CheckClaims
/-- The address of the first index. -/
abbrev indices : Var := ⟨0⟩
/-- How many indices there are. -/
abbrev count : Var := ⟨1⟩
/-- The claim being checked. -/
abbrev i : Var := ⟨2⟩
/-- The claim's index. -/
abbrev claim : Var := ⟨3⟩
/-- A position found by a search. -/
abbrev found : Var := ⟨4⟩
/-- The answer: zero, or the first refusal. -/
abbrev answer : Var := ⟨5⟩
/-- One of the claim's strict ancestors. -/
abbrev above : Var := ⟨6⟩

/--
Refuses an index set that cannot be verified soundly: arguments indices, count.

Answers zero, or the code of the first refusal: no index, an index repeated, then per claim in order an index of
zero, the root, or a claimed strict ancestor.
-/
def fn : Fn :=
  { params := 2, vars := 7, result := answer,
    body := .block [answer ::= 0,
      ifElse (eq count 0) [answer ::= 8]
        [i ::= 0,
          -- A repeat is a claim found earlier than its own position.
          while_ (lt i count) [callInto found "ssz_branch_find" [indices, 8, i, ld (indices + 8 * i)],
            ifElse (ne found i) [answer ::= 9, i ::= count] [i ::= i + 1]],
          i ::= 0,
          when (eq answer 0) [while_ (lt i count) [claim ::= ld (indices + 8 * i),
            ifElse (eq claim 0) [answer ::= 3, i ::= count]
              [ifElse (eq claim 1) [answer ::= 4, i ::= count]
                [above ::= .shr claim 1,
                  -- The strict ancestors below the root, each looked for among the claims.
                  while_ (lt 1 above) [callInto found "ssz_branch_find" [indices, 8, count, above],
                    ifElse (ne found count) [answer ::= 10, above ::= 0] [above ::= .shr above 1]],
                  ifElse (ne answer 0) [i ::= count] [i ::= i + 1]]]]]]] }
end CheckClaims

namespace CollectPaths
/-- The address of the first index. -/
abbrev indices : Var := ⟨0⟩
/-- How many indices there are. -/
abbrev count : Var := ⟨1⟩
/-- Where the path nodes go. -/
abbrev paths : Var := ⟨2⟩
/-- The claim being walked. -/
abbrev i : Var := ⟨3⟩
/-- A node of the claim's path. -/
abbrev node : Var := ⟨4⟩
/-- How many path nodes are written. -/
abbrev n : Var := ⟨5⟩

/--
The paths of several claims, each from the claim up to below the root, one after the other: arguments indices,
count, paths.

Returns the number of path nodes written, 8 bytes each.
-/
def fn : Fn :=
  { params := 3, vars := 6, result := n,
    body := .block [n ::= 0, i ::= 0,
      while_ (lt i count) [node ::= ld (indices + 8 * i),
        while_ (lt 1 node) [st (paths + 8 * n) node, n ::= n + 1, node ::= .shr node 1],
        i ::= i + 1]] }
end CollectPaths

namespace Candidates
/-- The address of the first path node. -/
abbrev paths : Var := ⟨0⟩
/-- How many path nodes there are. -/
abbrev count : Var := ⟨1⟩
/-- Where the candidates go. -/
abbrev out : Var := ⟨2⟩
/-- The path node being read. -/
abbrev i : Var := ⟨3⟩
/-- Its sibling. -/
abbrev sibling : Var := ⟨4⟩
/-- A position found by a search. -/
abbrev found : Var := ⟨5⟩
/-- How many candidates are written. -/
abbrev n : Var := ⟨6⟩

/--
The siblings of path nodes that are no path node themselves, in order and possibly repeated: arguments paths,
count, out.

Returns the number written, 8 bytes each.
-/
def fn : Fn :=
  { params := 3, vars := 7, result := n,
    body := .block [n ::= 0, i ::= 0,
      while_ (lt i count) [sibling ::= ld (paths + 8 * i) ^^^ 1,
        callInto found "ssz_branch_find" [paths, 8, count, sibling],
        when (eq found count) [st (out + 8 * n) sibling, n ::= n + 1],
        i ::= i + 1]] }
end Candidates

namespace SelectDesc
/-- The address of the first candidate. -/
abbrev cands : Var := ⟨0⟩
/-- How many candidates there are. -/
abbrev count : Var := ⟨1⟩
/-- Where the sorted values go. -/
abbrev out : Var := ⟨2⟩
/-- One once a value has been written, so later ones stay below the last. -/
abbrev started : Var := ⟨3⟩
/-- The last value written. -/
abbrev last : Var := ⟨4⟩
/-- One while the pass found a value to write. -/
abbrev found : Var := ⟨5⟩
/-- The largest value of this pass. -/
abbrev best : Var := ⟨6⟩
/-- The candidate being read. -/
abbrev i : Var := ⟨7⟩
/-- Its value. -/
abbrev c : Var := ⟨8⟩
/-- How many values are written. -/
abbrev n : Var := ⟨9⟩
/-- One while another pass is due. -/
abbrev more : Var := ⟨10⟩

/--
The distinct candidates, largest first: arguments cands, count, out.

Each pass writes the largest candidate below the last one written.
Returns the number written, 8 bytes each.
-/
def fn : Fn :=
  { params := 3, vars := 11, result := n,
    body := .block [n ::= 0, started ::= 0, last ::= 0, more ::= 1,
      while_ more [found ::= 0, best ::= 0, i ::= 0,
        while_ (lt i count) [c ::= ld (cands + 8 * i),
          -- A value qualifies below the last one written, and wins above the best so far.
          when ((eq started 0) ||| (lt c last))
            [when ((eq found 0) ||| (lt best c)) [best ::= c, found ::= 1]],
          i ::= i + 1],
        ifElse found [st (out + 8 * n) best, n ::= n + 1, last ::= best, started ::= 1] [more ::= 0]]] }
end SelectDesc

namespace HelperIndices
/-- The address of the first index. -/
abbrev indices : Var := ⟨0⟩
/-- How many indices there are. -/
abbrev count : Var := ⟨1⟩
/-- A scratch area for the paths and the candidates. -/
abbrev scratch : Var := ⟨2⟩
/-- Where the helper indices go. -/
abbrev helpers : Var := ⟨3⟩
/-- Where their number goes. -/
abbrev out : Var := ⟨4⟩
/-- The answer. -/
abbrev answer : Var := ⟨5⟩
/-- How many path nodes there are. -/
abbrev paths : Var := ⟨6⟩
/-- How many candidates there are. -/
abbrev cands : Var := ⟨7⟩
/-- How many helper indices there are. -/
abbrev n : Var := ⟨8⟩

/--
The indices of the nodes a multiproof carries, largest first: arguments indices, count, scratch, helpers, out.

The scratch area takes 1024 bytes per index: the paths, then the candidates.
Answers zero and writes the number of helper indices to out, or answers the code of the first refusal.
-/
def fn : Fn :=
  { params := 5, vars := 9, result := answer,
    body := .block [callInto answer "ssz_branch_check_claims" [indices, count],
      when (eq answer 0) [callInto paths "ssz_branch_paths" [indices, count, scratch],
        callInto cands "ssz_branch_candidates" [scratch, paths, scratch + 512 * count],
        callInto n "ssz_branch_select" [scratch + 512 * count, cands, helpers],
        st out n]] }
end HelperIndices

namespace FoldParents
/-- The address of the first entry of the node set. -/
abbrev src : Var := ⟨0⟩
/-- How many entries it has. -/
abbrev count : Var := ⟨1⟩
/-- Where the parents go, as entries. -/
abbrev dst : Var := ⟨2⟩
/-- The level being folded. -/
abbrev depth : Var := ⟨3⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨4⟩
/-- Where the number of parents goes. -/
abbrev out : Var := ⟨5⟩
/-- The entry being read. -/
abbrev i : Var := ⟨6⟩
/-- Its index. -/
abbrev index : Var := ⟨7⟩
/-- Its level. -/
abbrev lv : Var := ⟨8⟩
/-- The position of its sibling. -/
abbrev j : Var := ⟨9⟩
/-- How many parents are written. -/
abbrev k : Var := ⟨10⟩
/-- The answer: zero, or the first refusal. -/
abbrev answer : Var := ⟨11⟩
/-- A hashing call's result. -/
abbrev got : Var := ⟨12⟩
/-- Zero unless some hashing call found no kernel. -/
abbrev status : Var := ⟨13⟩

/--
The parents of one level of a node set, in order: arguments src, count, dst, depth, ctx, out.

An even index at the level is hashed with the entry holding the next index, which must exist.
An odd index at the level needs an entry holding the one before.
Answers zero and writes the number of parents to out, or answers 11 or 2.
-/
def fn : Fn :=
  { params := 6, vars := 14, result := answer,
    body := .block [k ::= 0, answer ::= 0, status ::= 0, i ::= 0,
      while_ (lt i count) [index ::= ld (src + 40 * i),
        callInto lv "ssz_branch_level" [index],
        when (eq lv depth)
          [ifElse (eq (index &&& 1) 0)
            [callInto j "ssz_branch_find" [src, 40, count, index + 1],
              ifElse (eq j count) [answer ::= 11, i ::= count]
                [callInto got "ssz_hash_columns" [dst + 40 * k + 8, src + 40 * i + 8, src + 40 * j + 8, 1, ctx],
                  status ::= status ||| got, st (dst + 40 * k) (.shr index 1), k ::= k + 1]]
            [callInto j "ssz_branch_find" [src, 40, count, index - 1],
              when (eq j count) [answer ::= 11, i ::= count]]],
        i ::= i + 1],
      when (ne status 0) [answer ::= 2],
      st out k] }
end FoldParents

namespace FoldKept
/-- The address of the first entry of the node set. -/
abbrev src : Var := ⟨0⟩
/-- How many entries it has. -/
abbrev count : Var := ⟨1⟩
/-- Where the kept entries go. -/
abbrev dst : Var := ⟨2⟩
/-- The level being folded. -/
abbrev depth : Var := ⟨3⟩
/-- The entry being read. -/
abbrev i : Var := ⟨4⟩
/-- Its level. -/
abbrev lv : Var := ⟨5⟩
/-- How many entries are kept. -/
abbrev k : Var := ⟨6⟩

/-- The entries off one level of a node set, copied in order: arguments src, count, dst, depth. Returns how many. -/
def fn : Fn :=
  { params := 4, vars := 7, result := k,
    body := .block [k ::= 0, i ::= 0,
      while_ (lt i count) [callInto lv "ssz_branch_level" [ld (src + 40 * i)],
        when (ne lv depth) ([st (dst + 40 * k) (ld (src + 40 * i))] ++
          copy32 (dst + 40 * k + 8) (src + 40 * i + 8) ++ [k ::= k + 1]),
        i ::= i + 1]] }
end FoldKept

namespace VerifyMultiproof
/-- The job the caller filled. -/
abbrev job : Var := ⟨0⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨1⟩
/-- The address of the first leaf. -/
abbrev leaves : Var := ⟨2⟩
/-- How many leaves there are. -/
abbrev leafCount : Var := ⟨3⟩
/-- The address of the first proof node. -/
abbrev proof : Var := ⟨4⟩
/-- How many proof nodes there are. -/
abbrev proofCount : Var := ⟨5⟩
/-- The address of the first index. -/
abbrev indices : Var := ⟨6⟩
/-- How many indices there are. -/
abbrev count : Var := ⟨7⟩
/-- The scratch area. -/
abbrev scratch : Var := ⟨8⟩
/-- The answer. -/
abbrev answer : Var := ⟨9⟩
/-- Where the helper indices are. -/
abbrev helpers : Var := ⟨10⟩
/-- The node set being folded. -/
abbrev cur : Var := ⟨11⟩
/-- The node set being written. -/
abbrev nxt : Var := ⟨12⟩
/-- How many entries the node set has. -/
abbrev size : Var := ⟨13⟩
/-- An entry position. -/
abbrev i : Var := ⟨14⟩
/-- The level being folded. -/
abbrev depth : Var := ⟨15⟩
/-- A level, or a count a call returns. -/
abbrev t : Var := ⟨16⟩
/-- The address of the swapped-out node set. -/
abbrev tmp : Var := ⟨17⟩

/--
Whether several leaves and the proof nodes rebuild a root: arguments job, ctx.

The job holds eight words:

```text
    job + 0    the address of the leaves, 32 bytes each
    job + 8    the number of leaves
    job + 16   the address of the proof nodes, 32 bytes each
    job + 24   the number of proof nodes
    job + 32   the address of the generalized indices, 8 bytes each
    job + 40   the number of indices
    job + 48   the address of the expected root
    job + 56   the address of a scratch area, apart from everything else
```

The scratch area takes 8 + 1536 n + 160 (n + p) bytes for n indices and p proof nodes.
-/
def fn : Fn :=
  { params := 2, vars := 18, result := answer,
    body := .block [leaves ::= ld job, leafCount ::= ld (job + 8), proof ::= ld (job + 16),
      proofCount ::= ld (job + 24), indices ::= ld (job + 32), count ::= ld (job + 40), scratch ::= ld (job + 56),
      ifElse (ne leafCount count) [answer ::= 6]
        [helpers ::= scratch + 8 + 1024 * count,
          callInto answer "ssz_branch_helpers" [indices, count, scratch + 8, helpers, scratch],
          when (eq answer 0)
            [ifElse (ne (ld scratch) proofCount) [answer ::= 7]
              [cur ::= scratch + 8 + 1536 * count, size ::= count + proofCount,
                nxt ::= cur + 80 * size,
                -- The leaves at their indices, then the proof nodes at the helper indices.
                i ::= 0,
                while_ (lt i count) ([st (cur + 40 * i) (ld (indices + 8 * i))] ++
                  copy32 (cur + 40 * i + 8) (leaves + 32 * i) ++ [i ::= i + 1]),
                i ::= 0,
                while_ (lt i proofCount) ([st (cur + 40 * (count + i)) (ld (helpers + 8 * i))] ++
                  copy32 (cur + 40 * (count + i) + 8) (proof + 32 * i) ++ [i ::= i + 1]),
                -- The fold starts at the deepest level any entry sits on.
                depth ::= 0, i ::= 0,
                while_ (lt i size) [callInto t "ssz_branch_level" [ld (cur + 40 * i)],
                  when (lt depth t) [depth ::= t], i ::= i + 1],
                while_ (lt 0 depth) [
                  callInto answer "ssz_branch_fold_parents" [cur, size, nxt, depth, ctx, scratch],
                  ifElse (ne answer 0) [depth ::= 0]
                    [callInto t "ssz_branch_fold_kept" [cur, size, nxt + 40 * ld scratch, depth],
                      size ::= ld scratch + t, tmp ::= cur, cur ::= nxt, nxt ::= tmp, depth ::= depth - 1]],
                when (eq answer 0)
                  [callInto i "ssz_branch_find" [cur, 40, size, 1],
                    ifElse (eq i size) [answer ::= 11]
                      [callInto answer "ssz_branch_same" [cur + 40 * i + 8, ld (job + 48)]]]]]]] }
end VerifyMultiproof

/-- The branch and multiproof drivers, each under its exported name. -/
def branchFns : List (String × Fn) :=
  [("ssz_branch_level", Level.fn), ("ssz_branch_find", Find.fn), ("ssz_branch_same", Same.fn),
    ("ssz_verify_branch", VerifyBranch.fn), ("ssz_branch_check_claims", CheckClaims.fn),
    ("ssz_branch_paths", CollectPaths.fn), ("ssz_branch_candidates", Candidates.fn),
    ("ssz_branch_select", SelectDesc.fn), ("ssz_branch_helpers", HelperIndices.fn),
    ("ssz_branch_fold_parents", FoldParents.fn), ("ssz_branch_fold_kept", FoldKept.fn),
    ("ssz_verify_multiproof", VerifyMultiproof.fn)]

/-- Every branch driver fits the compiler's assumptions. -/
theorem branchFns_wf : branchFns.all (fun f => f.2.wf) = true := by
  decide +kernel

end EthLib.Consensus.Ssz.Native.Driver
