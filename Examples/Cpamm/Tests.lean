import Examples.Cpamm.Contract

/-!
CPAMM smoke tests. The CALL oracle here always returns `true` for
`transfer`/`transferFrom`; it is not a conforming ERC-20.
-/

open Lsc Lsc.Stdlib Cpamm

namespace Cpamm

def smokeOracle : Oracle ExtState where
  call _addr sel _args ext :=
    if sel == 0x23b872dd || sel == 0xa9059cbb then some ([1], ext) else none
  view _addr sel _args _ext :=
    if sel == 0x70a08231 then [100000] else []

def smokeCtx : Ctx := { sender := 2, self := 1 }

def smokeEmpty : World where
  self := {
    token0 := ⟨10⟩, token1 := ⟨11⟩
    reserve0 := 0, reserve1 := 0
    totalShares := 0, shares := fun _ => 0
    owner := 2, feeTo := 0, protocolShareBps := 0
    protocolFees0 := 0, protocolFees1 := 0 }
  ext := default
  oracle := smokeOracle

def smokePool : World where
  self := {
    token0 := ⟨10⟩, token1 := ⟨11⟩
    reserve0 := 1000, reserve1 := 2000
    totalShares := 1000
    shares := fun a => if a = (2 : Address) then 1000 else 0
    owner := 2, feeTo := 0, protocolShareBps := 0
    protocolFees0 := 0, protocolFees1 := 0 }
  ext := default
  oracle := smokeOracle

def smokePoolProto : World where
  self := {
    token0 := ⟨10⟩, token1 := ⟨11⟩
    reserve0 := 1000, reserve1 := 2000
    totalShares := 1000
    shares := fun a => if a = (2 : Address) then 1000 else 0
    owner := 2, feeTo := 3, protocolShareBps := 10000
    protocolFees0 := 0, protocolFees1 := 0 }
  ext := default
  oracle := smokeOracle

end Cpamm

#guard
  (match Lsc.Tx.run (Cpamm.addLiquidity 100 200) Cpamm.smokeCtx Cpamm.smokeEmpty with
    | .error (.user .InsufficientLiquidity) => true
    | _ => false)

#guard
  (match Lsc.Tx.run (Cpamm.addLiquidity 2000 4000) Cpamm.smokeCtx Cpamm.smokeEmpty with
    | .ok (n, w') =>
        n.raw == 1000 && w'.self.totalShares.raw == 2000
          && (w'.self.shares 2).raw == 1000 && (w'.self.shares 0).raw == 1000
    | _ => false)

#guard
  (match Lsc.Tx.run Cpamm.getReserves Cpamm.smokeCtx Cpamm.smokePool with
    | .ok (p, _) => p.1.raw == 1000 && p.2.raw == 2000
    | _ => false)

#guard
  (match Lsc.Tx.run (Cpamm.sharesOf 2) Cpamm.smokeCtx Cpamm.smokePool with
    | .ok (n, _) => n.raw == 1000
    | _ => false)

#guard
  (match Lsc.Tx.run Cpamm.protocolFees Cpamm.smokeCtx Cpamm.smokePool with
    | .ok (p, _) => p.1.raw == 0 && p.2.raw == 0
    | _ => false)

-- dx=100, dxF=99, out=⌊2000·99/1099⌋=180, feeTo=0 so proto=0, r0'=1100, r1'=1820
#guard
  (match Lsc.Tx.run (Cpamm.swap0for1 100 0) Cpamm.smokeCtx Cpamm.smokePool with
    | .ok (out, w') =>
        out.raw == 180 && w'.self.reserve0 == 1100 && w'.self.reserve1 == 1820
          && w'.self.protocolFees0 == 0 && w'.self.protocolFees1 == 0
    | _ => false)

-- 100% protocol take: proto=1, r0'=1099, bucket0=1, r1' still 1820
#guard
  (match Lsc.Tx.run (Cpamm.swap0for1 100 0) Cpamm.smokeCtx Cpamm.smokePoolProto with
    | .ok (_, w') =>
        w'.self.reserve0 == 1099 && w'.self.reserve1 == 1820
          && w'.self.protocolFees0 == 1 && w'.self.protocolFees1 == 0
    | _ => false)

-- share > BPS: fee=1, proto=⌊1·20000/10000⌋=2 > fee → FeeTooHigh
#guard
  (match Lsc.Tx.run (Cpamm.swap0for1 100 0) Cpamm.smokeCtx
      { Cpamm.smokePoolProto with
        self := { Cpamm.smokePoolProto.self with protocolShareBps := 20000 } } with
    | .error (.user .FeeTooHigh) => true
    | _ => false)

#guard
  (match Lsc.Tx.run (Cpamm.setProtocolShare 5000) Cpamm.smokeCtx Cpamm.smokePool with
    | .ok (_, w') => w'.self.protocolShareBps == 5000 && w'.self.protocolFees0 == 0
    | _ => false)

#guard
  (match Lsc.Tx.run (Cpamm.setProtocolShare 5000)
      { Cpamm.smokeCtx with sender := 9 } Cpamm.smokePool with
    | .error (.user .NotOwner) => true
    | _ => false)

#guard
  (match Lsc.Tx.run (Cpamm.setProtocolShare 10001) Cpamm.smokeCtx Cpamm.smokePool with
    | .error (.user .FeeTooHigh) => true
    | _ => false)
