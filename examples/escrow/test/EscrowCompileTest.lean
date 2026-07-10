import Escrow
import Lsc.Compile.Yul

open Lsc Lsc.Compile

namespace EscrowCompileTest

private def releaseYul : String :=
  match Compile.stmtToYul Escrow.config Escrow.releaseImpl with
  | .ok yul => yul
  | .error e => panic! e

theorem release_has_one_transfer_call :
    (releaseYul.splitOn "call(gas()").length = 2 := by native_decide

theorem release_has_no_safeerc20_storage_call :
    releaseYul.contains "safeERC20" = false := by native_decide

theorem release_binds_bool_return :
    releaseYul.contains "mload(0x" = true := by native_decide

theorem release_checks_ok_before_continue :
    releaseYul.contains "iszero(" = true := by native_decide

theorem release_bytecode_contains_transfer_selector :
    Escrow.bytecodeHex.contains "a9059cbb" = true := by native_decide

theorem release_bytecode_loads_token_slot_before_call :
    Escrow.bytecodeHex.contains "600254" = true := by native_decide

theorem release_bytecode_call_avoids_gas_dup4 :
    Escrow.bytecodeHex.contains "5a83" = false := by native_decide

theorem release_bytecode_call_uses_gas_dup_token :
    Escrow.bytecodeHex.contains "5a81" = true := by native_decide

#eval IO.println releaseYul

end EscrowCompileTest
