// selector → function  (hex and decimal; `switch` cases print decimal)
//   0xa9059cbb  (2835717307)  transfer(address,uint256)
//   0x095ea7b3  (157198259)  approve(address,uint256)
//   0x23b872dd  (599290589)  transferFrom(address,address,uint256)
//   0x40c10f19  (1086394137)  mint(address,uint256)
//   0x42966c68  (1117154408)  burn(uint256)
//   0x70a08231  (1889567281)  balanceOf(address)
//   0xdd62ed3e  (3714247998)  allowance(address,address)
//   0x18160ddd  (404098525)  totalSupply()

object "Token" {
    code {
        codecopy(128, sub(codesize(), 64), 64)
        let constructor_0 := mload(128)
        let constructor_1 := mload(160)
        sstore(0, constructor_0)
        sstore(1, constructor_1)
        mstore(0, constructor_0)
        mstore(32, 2)
        sstore(keccak256(0, 64), constructor_1)
        mstore(128, 0)
        mstore(160, constructor_0)
        mstore(192, constructor_1)
        log1(128, 96, 100389287136786176327247604509743168900146139575972864366142685224231313322991)
        datacopy(0, dataoffset("runtime"), datasize("runtime"))
        return(0, datasize("runtime"))
    }
    object "runtime" {
        code {
            if memoryguard(256) {
            }
            {
                if lt(calldatasize(), 4) {
                    revert(0, 0)
                }
            }
            switch shr(224, calldataload(0))
            case 2835717307 { // transfer(address,uint256)
                {
                    if lt(calldatasize(), 68) {
                        revert(0, 0)
                    }
                }
                {
                    let transfer_0 := calldataload(4)
                    let transfer_1 := calldataload(36)
                    let transfer_2 := caller()
                    mstore(0, transfer_2)
                    mstore(32, 2)
                    let transfer_3 := sload(keccak256(0, 64))
                    if iszero(iszero(lt(transfer_3, transfer_1))) {
                        mstore(128, shl(224, 4107696312))
                        revert(128, 4)
                    }
                    if lt(transfer_3, transfer_1) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let transfer_4 := sub(transfer_3, transfer_1)
                    mstore(0, transfer_2)
                    mstore(32, 2)
                    sstore(keccak256(0, 64), transfer_4)
                    mstore(0, transfer_0)
                    mstore(32, 2)
                    let transfer_5 := sload(keccak256(0, 64))
                    let transfer_6 := add(transfer_5, transfer_1)
                    if lt(transfer_6, transfer_5) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    mstore(0, transfer_0)
                    mstore(32, 2)
                    sstore(keccak256(0, 64), transfer_6)
                    mstore(128, transfer_2)
                    mstore(160, transfer_0)
                    mstore(192, transfer_1)
                    log1(128, 96, 100389287136786176327247604509743168900146139575972864366142685224231313322991)
                    stop()
                }
            }
            case 157198259 { // approve(address,uint256)
                {
                    if lt(calldatasize(), 68) {
                        revert(0, 0)
                    }
                }
                {
                    let approve_0 := calldataload(4)
                    let approve_1 := calldataload(36)
                    let approve_2 := caller()
                    mstore(0, approve_2)
                    mstore(32, 3)
                    mstore(32, keccak256(0, 64))
                    mstore(0, approve_0)
                    sstore(keccak256(0, 64), approve_1)
                    mstore(128, approve_2)
                    mstore(160, approve_0)
                    mstore(192, approve_1)
                    log1(128, 96, 63486140976153616755203102783360879283472101686154884697241723088393386309925)
                    stop()
                }
            }
            case 599290589 { // transferFrom(address,address,uint256)
                {
                    if lt(calldatasize(), 100) {
                        revert(0, 0)
                    }
                }
                {
                    let transferFrom_0 := calldataload(4)
                    let transferFrom_1 := calldataload(36)
                    let transferFrom_2 := calldataload(68)
                    let transferFrom_3 := caller()
                    mstore(0, transferFrom_0)
                    mstore(32, 3)
                    mstore(32, keccak256(0, 64))
                    mstore(0, transferFrom_3)
                    let transferFrom_4 := sload(keccak256(0, 64))
                    if iszero(iszero(lt(transferFrom_4, transferFrom_2))) {
                        mstore(128, shl(224, 331228459))
                        revert(128, 4)
                    }
                    mstore(0, transferFrom_0)
                    mstore(32, 2)
                    let transferFrom_5 := sload(keccak256(0, 64))
                    if iszero(iszero(lt(transferFrom_5, transferFrom_2))) {
                        mstore(128, shl(224, 4107696312))
                        revert(128, 4)
                    }
                    if lt(transferFrom_4, transferFrom_2) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let transferFrom_6 := sub(transferFrom_4, transferFrom_2)
                    mstore(0, transferFrom_0)
                    mstore(32, 3)
                    mstore(32, keccak256(0, 64))
                    mstore(0, transferFrom_3)
                    sstore(keccak256(0, 64), transferFrom_6)
                    if lt(transferFrom_5, transferFrom_2) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let transferFrom_7 := sub(transferFrom_5, transferFrom_2)
                    mstore(0, transferFrom_0)
                    mstore(32, 2)
                    sstore(keccak256(0, 64), transferFrom_7)
                    mstore(0, transferFrom_1)
                    mstore(32, 2)
                    let transferFrom_8 := sload(keccak256(0, 64))
                    let transferFrom_9 := add(transferFrom_8, transferFrom_2)
                    if lt(transferFrom_9, transferFrom_8) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    mstore(0, transferFrom_1)
                    mstore(32, 2)
                    sstore(keccak256(0, 64), transferFrom_9)
                    mstore(128, transferFrom_0)
                    mstore(160, transferFrom_1)
                    mstore(192, transferFrom_2)
                    log1(128, 96, 100389287136786176327247604509743168900146139575972864366142685224231313322991)
                    stop()
                }
            }
            case 1086394137 { // mint(address,uint256)
                {
                    if lt(calldatasize(), 68) {
                        revert(0, 0)
                    }
                }
                {
                    let mint_0 := calldataload(4)
                    let mint_1 := calldataload(36)
                    let mint_2 := caller()
                    let mint_3 := sload(0)
                    if iszero(eq(mint_2, mint_3)) {
                        mstore(128, shl(224, 818771057))
                        revert(128, 4)
                    }
                    let mint_4 := sload(1)
                    let mint_5 := add(mint_4, mint_1)
                    if lt(mint_5, mint_4) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    sstore(1, mint_5)
                    mstore(0, mint_0)
                    mstore(32, 2)
                    let mint_6 := sload(keccak256(0, 64))
                    let mint_7 := add(mint_6, mint_1)
                    if lt(mint_7, mint_6) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    mstore(0, mint_0)
                    mstore(32, 2)
                    sstore(keccak256(0, 64), mint_7)
                    mstore(128, 0)
                    mstore(160, mint_0)
                    mstore(192, mint_1)
                    log1(128, 96, 100389287136786176327247604509743168900146139575972864366142685224231313322991)
                    stop()
                }
            }
            case 1117154408 { // burn(uint256)
                {
                    if lt(calldatasize(), 36) {
                        revert(0, 0)
                    }
                }
                {
                    let burn_0 := calldataload(4)
                    let burn_1 := caller()
                    mstore(0, burn_1)
                    mstore(32, 2)
                    let burn_2 := sload(keccak256(0, 64))
                    switch iszero(lt(burn_2, burn_0))
                    case 0 {
                        mstore(128, shl(224, 4107696312))
                        revert(128, 4)
                        mstore(128, burn_1)
                        mstore(160, 0)
                        mstore(192, burn_0)
                        log1(128, 96, 100389287136786176327247604509743168900146139575972864366142685224231313322991)
                        stop()
                    }
                    default {
                        if lt(burn_2, burn_0) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        let burn_3 := sub(burn_2, burn_0)
                        mstore(0, burn_1)
                        mstore(32, 2)
                        sstore(keccak256(0, 64), burn_3)
                        let burn_4 := sload(1)
                        if lt(burn_4, burn_0) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        let burn_5 := sub(burn_4, burn_0)
                        sstore(1, burn_5)
                        mstore(128, burn_1)
                        mstore(160, 0)
                        mstore(192, burn_0)
                        log1(128, 96, 100389287136786176327247604509743168900146139575972864366142685224231313322991)
                        stop()
                    }
                }
            }
            case 1889567281 { // balanceOf(address)
                {
                    if lt(calldatasize(), 36) {
                        revert(0, 0)
                    }
                }
                {
                    let balanceOf_0 := calldataload(4)
                    mstore(0, balanceOf_0)
                    mstore(32, 2)
                    let balanceOf_1 := sload(keccak256(0, 64))
                    mstore(128, balanceOf_1)
                    return(128, 32)
                }
            }
            case 3714247998 { // allowance(address,address)
                {
                    if lt(calldatasize(), 68) {
                        revert(0, 0)
                    }
                }
                {
                    let allowance_0 := calldataload(4)
                    let allowance_1 := calldataload(36)
                    mstore(0, allowance_0)
                    mstore(32, 3)
                    mstore(32, keccak256(0, 64))
                    mstore(0, allowance_1)
                    let allowance_2 := sload(keccak256(0, 64))
                    mstore(128, allowance_2)
                    return(128, 32)
                }
            }
            case 404098525 { // totalSupply()
                {
                    if lt(calldatasize(), 4) {
                        revert(0, 0)
                    }
                }
                {
                    let totalSupply_0 := sload(1)
                    mstore(128, totalSupply_0)
                    return(128, 32)
                }
            }
            default {
                revert(0, 0)
            }
        }
    }
}
