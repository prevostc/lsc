// selector → function  (hex and decimal; `switch` cases print decimal)
//   0xd0e30db0  (3504541104)  deposit()
//   0x2e1a7d4d  (773487949)  withdraw(uint256)
//   0xa9059cbb  (2835717307)  transfer(address,uint256)
//   0x23b872dd  (599290589)  transferFrom(address,address,uint256)
//   0x095ea7b3  (157198259)  approve(address,uint256)
//   0x18160ddd  (404098525)  totalSupply()
//   0x70a08231  (1889567281)  balanceOf(address)
//   0xdd62ed3e  (3714247998)  allowance(address,address)

{
    if memoryguard(256) {
    }
    if tload(0) {
        revert(0, 0)
    }
    {
        if lt(calldatasize(), 4) {
            revert(0, 0)
        }
    }
    switch shr(224, calldataload(0))
    case 3504541104 { // deposit()
        {
            if lt(calldatasize(), 4) {
                revert(0, 0)
            }
        }
        if lt(selfbalance(), callvalue()) {
            revert(0, 0)
        }
        {
            let deposit_0 := caller()
            let deposit_1 := callvalue()
            mstore(0, deposit_0)
            mstore(32, 0)
            let deposit_2 := sload(keccak256(0, 64))
            let deposit_3 := add(deposit_2, deposit_1)
            if lt(deposit_3, deposit_2) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            mstore(0, deposit_0)
            mstore(32, 0)
            sstore(keccak256(0, 64), deposit_3)
            let deposit_4 := sload(2)
            let deposit_5 := add(deposit_4, deposit_1)
            if lt(deposit_5, deposit_4) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            sstore(2, deposit_5)
            mstore(128, deposit_0)
            mstore(160, deposit_1)
            log1(128, 64, 102222681472383059465863322013072701928378550215632170212813623808969952268444)
            stop()
        }
    }
    case 773487949 { // withdraw(uint256)
        {
            if lt(calldatasize(), 36) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
        }
        tstore(0, 1)
        {
            let withdraw_0 := calldataload(4)
            let withdraw_1 := caller()
            mstore(0, withdraw_1)
            mstore(32, 0)
            let withdraw_2 := sload(keccak256(0, 64))
            if lt(withdraw_2, withdraw_0) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            let withdraw_3 := sub(withdraw_2, withdraw_0)
            mstore(0, withdraw_1)
            mstore(32, 0)
            sstore(keccak256(0, 64), withdraw_3)
            let withdraw_4 := sload(2)
            if lt(withdraw_4, withdraw_0) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            let withdraw_5 := sub(withdraw_4, withdraw_0)
            sstore(2, withdraw_5)
            let withdraw_6 := 0
            {
                let withdraw__ok_6 := call(1000000, withdraw_1, withdraw_0, 0, 0, 0, 0)
                withdraw_6 := withdraw__ok_6
            }
            if iszero(eq(withdraw_6, 1)) {
                mstore(128, shl(224, 2428038168))
                revert(128, 4)
            }
            mstore(128, withdraw_1)
            mstore(160, withdraw_0)
            log1(128, 64, 57810043145978950376228313794938171962422655018555593468903716172405399886693)
            tstore(0, 0)
            stop()
        }
    }
    case 2835717307 { // transfer(address,uint256)
        {
            if lt(calldatasize(), 68) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
        }
        {
            let transfer_0 := calldataload(4)
            let transfer_1 := calldataload(36)
            let transfer_2 := caller()
            mstore(0, transfer_2)
            mstore(32, 0)
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
            mstore(32, 0)
            sstore(keccak256(0, 64), transfer_4)
            mstore(0, transfer_0)
            mstore(32, 0)
            let transfer_5 := sload(keccak256(0, 64))
            let transfer_6 := add(transfer_5, transfer_1)
            if lt(transfer_6, transfer_5) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            mstore(0, transfer_0)
            mstore(32, 0)
            sstore(keccak256(0, 64), transfer_6)
            mstore(128, transfer_2)
            mstore(160, transfer_0)
            mstore(192, transfer_1)
            log1(128, 96, 100389287136786176327247604509743168900146139575972864366142685224231313322991)
            mstore(128, 1)
            return(128, 32)
        }
    }
    case 599290589 { // transferFrom(address,address,uint256)
        {
            if lt(calldatasize(), 100) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
        }
        {
            let transferFrom_0 := calldataload(4)
            let transferFrom_1 := calldataload(36)
            let transferFrom_2 := calldataload(68)
            let transferFrom_3 := caller()
            mstore(0, transferFrom_0)
            mstore(32, 1)
            mstore(32, keccak256(0, 64))
            mstore(0, transferFrom_3)
            let transferFrom_4 := sload(keccak256(0, 64))
            if iszero(iszero(lt(transferFrom_4, transferFrom_2))) {
                mstore(128, shl(224, 331228459))
                revert(128, 4)
            }
            mstore(0, transferFrom_0)
            mstore(32, 0)
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
            mstore(32, 1)
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
            mstore(32, 0)
            sstore(keccak256(0, 64), transferFrom_7)
            mstore(0, transferFrom_1)
            mstore(32, 0)
            let transferFrom_8 := sload(keccak256(0, 64))
            let transferFrom_9 := add(transferFrom_8, transferFrom_2)
            if lt(transferFrom_9, transferFrom_8) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            mstore(0, transferFrom_1)
            mstore(32, 0)
            sstore(keccak256(0, 64), transferFrom_9)
            mstore(128, transferFrom_0)
            mstore(160, transferFrom_1)
            mstore(192, transferFrom_2)
            log1(128, 96, 100389287136786176327247604509743168900146139575972864366142685224231313322991)
            mstore(128, 1)
            return(128, 32)
        }
    }
    case 157198259 { // approve(address,uint256)
        {
            if lt(calldatasize(), 68) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
        }
        {
            let approve_0 := calldataload(4)
            let approve_1 := calldataload(36)
            let approve_2 := caller()
            mstore(0, approve_2)
            mstore(32, 1)
            mstore(32, keccak256(0, 64))
            mstore(0, approve_0)
            sstore(keccak256(0, 64), approve_1)
            mstore(128, approve_2)
            mstore(160, approve_0)
            mstore(192, approve_1)
            log1(128, 96, 63486140976153616755203102783360879283472101686154884697241723088393386309925)
            mstore(128, 1)
            return(128, 32)
        }
    }
    case 404098525 { // totalSupply()
        {
            if lt(calldatasize(), 4) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
        }
        {
            let totalSupply_0 := sload(2)
            mstore(128, totalSupply_0)
            return(128, 32)
        }
    }
    case 1889567281 { // balanceOf(address)
        {
            if lt(calldatasize(), 36) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
        }
        {
            let balanceOf_0 := calldataload(4)
            mstore(0, balanceOf_0)
            mstore(32, 0)
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
        if callvalue() {
            revert(0, 0)
        }
        {
            let allowance_0 := calldataload(4)
            let allowance_1 := calldataload(36)
            mstore(0, allowance_0)
            mstore(32, 1)
            mstore(32, keccak256(0, 64))
            mstore(0, allowance_1)
            let allowance_2 := sload(keccak256(0, 64))
            mstore(128, allowance_2)
            return(128, 32)
        }
    }
    default {
        revert(0, 0)
    }
}
