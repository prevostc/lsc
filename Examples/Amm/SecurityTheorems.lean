import Examples.Amm.Security
import Examples.Amm.SecurityProof

/-!
AMM instances of the generic wealth theorems: LP shares as `claim`,
and solvency of each reserve token separately.
-/

open Lsc Lsc.Stdlib Lsc.Security Amm

namespace Amm

/-- `Inv` is preserved along well-formed traces for this pool, under env
steps that do not steal either reserve (`ammRely`). Both token-0 and
token-1 remain solvent: the pool's ERC-20 balances cover the
pro-rata claims. `k` (constant product) is a swap theorem, not `Inv`,
because `removeLiquidity` may decrease it by rounding. -/
theorem amm_solvent (self : Address) (tr : List (Step spec))
    (w : World Storage Ext Event)
    (hW : Wf self tr) (hR : RelyAlong (ammRely self) tr w) (h : Inv self w) :
    Solvent claim0 holdings0 self (run tr w) ∧
      Solvent claim1 holdings1 self (run tr w) :=
  Proof.amm_solvent self tr w hW hR h

/-- If `a` never authorised an AMM call (liquidity add/remove and swaps
as the sender; views never decrease shares), then `a`'s LP share
balance does not fall. Two-token env rely is required so neither
reserve can be stolen from under the pool. -/
theorem amm_no_unauthorized_extraction (self : Address)
    (tr : List (Step spec)) (w : World Storage Ext Event) (a : Address)
    (hw : Inv self w) (hW : Wf self tr) (hR : RelyAlong (ammRely self) tr w)
    (hA : NoAuthAlong Auth a tr w) :
    claim a w.self ≤ claim a (run tr w).self :=
  Proof.amm_no_unauthorized_extraction self tr w a hw hW hR hA

end Amm
