// selector → function  (hex and decimal; `switch` cases print decimal)
//   0xb6b55f25  (3065339685)  deposit(uint256)
//   0x2e1a7d4d  (773487949)  withdraw(uint256)
//   0xef8b30f7  (4018876663)  previewDeposit(uint256)
//   0x4cdad506  (1289409798)  previewRedeem(uint256)
//   0x8456cb59  (2220280665)  pause()
//   0x3f4ba83a  (1061922874)  unpause()
//   0x67dda112  (1742577938)  paused?()
//   0x313ce567  (826074471)  decimals()

object "Vault" {
    code {
        codecopy(128, sub(codesize(), 64), 64)
        let constructor_0 := mload(128)
        let constructor_1 := mload(160)
        sstore(4, constructor_0)
        sstore(5, constructor_1)
        sstore(3, 0)
        let constructor_2 := 0
        {
            let constructor__tok_2 := sload(5)
            mstore(128, shl(224, 826074471))
            let constructor__ok_2 := call(1000000, constructor__tok_2, 0, 128, 4, 128, 32)
            if iszero(constructor__ok_2) {
                revert(0, 0)
            }
            if lt(returndatasize(), 32) {
                revert(0, 0)
            }
            constructor_2 := mload(128)
        }
        sstore(6, constructor_2)
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
            case 3065339685 { // deposit(uint256)
                {
                    if lt(calldatasize(), 36) {
                        revert(0, 0)
                    }
                }
                {
                    let deposit_0 := calldataload(4)
                    let deposit_1 := sload(3)
                    if iszero(eq(deposit_1, 0)) {
                        mstore(128, shl(224, 2659711688))
                        revert(128, 4)
                    }
                    if iszero(lt(0, deposit_0)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    let deposit_2 := caller()
                    let deposit_3 := address()
                    let deposit_4 := sload(0)
                    let deposit_5 := sload(1)
                    switch eq(deposit_5, 0)
                    case 0 {
                        if iszero(deposit_4) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 18)
                            revert(128, 36)
                        }
                        let deposit_6 := mul(deposit_5, deposit_0)
                        if iszero(or(iszero(deposit_5), eq(div(deposit_6, deposit_5), deposit_0))) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        deposit_6 := div(deposit_6, deposit_4)
                        if iszero(lt(0, deposit_6)) {
                            mstore(128, shl(224, 2551308487))
                            revert(128, 4)
                        }
                        let deposit_7 := 0
                        {
                            let deposit__tok_7 := sload(5)
                            mstore(128, shl(224, 599290589))
                            mstore(132, deposit_2)
                            mstore(164, deposit_3)
                            mstore(196, deposit_0)
                            let deposit__ok_7 := call(1000000, deposit__tok_7, 0, 128, 100, 128, 32)
                            if iszero(deposit__ok_7) {
                                revert(0, 0)
                            }
                            if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                                revert(0, 0)
                            }
                            deposit_7 := 1
                        }
                        if iszero(iszero(eq(deposit_7, 0))) {
                            mstore(128, shl(224, 2428038168))
                            revert(128, 4)
                        }
                        let deposit_8 := add(deposit_4, deposit_0)
                        if lt(deposit_8, deposit_4) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        sstore(0, deposit_8)
                        let deposit_9 := add(deposit_6, deposit_5)
                        if lt(deposit_9, deposit_6) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        sstore(1, deposit_9)
                        mstore(0, deposit_2)
                        mstore(32, 2)
                        let deposit_10 := sload(keccak256(0, 64))
                        let deposit_11 := add(deposit_6, deposit_10)
                        if lt(deposit_11, deposit_6) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        mstore(0, deposit_2)
                        mstore(32, 2)
                        sstore(keccak256(0, 64), deposit_11)
                        mstore(128, deposit_2)
                        mstore(160, deposit_0)
                        mstore(192, deposit_6)
                        log1(128, 96, 65375163721362069710668505494972926144572850546638504720594393917789416593941)
                        mstore(128, deposit_6)
                        return(128, 32)
                    }
                    default {
                        let deposit_6 := deposit_0
                        if iszero(lt(0, deposit_6)) {
                            mstore(128, shl(224, 2551308487))
                            revert(128, 4)
                        }
                        let deposit_7 := 0
                        {
                            let deposit__tok_7 := sload(5)
                            mstore(128, shl(224, 599290589))
                            mstore(132, deposit_2)
                            mstore(164, deposit_3)
                            mstore(196, deposit_0)
                            let deposit__ok_7 := call(1000000, deposit__tok_7, 0, 128, 100, 128, 32)
                            if iszero(deposit__ok_7) {
                                revert(0, 0)
                            }
                            if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                                revert(0, 0)
                            }
                            deposit_7 := 1
                        }
                        if iszero(iszero(eq(deposit_7, 0))) {
                            mstore(128, shl(224, 2428038168))
                            revert(128, 4)
                        }
                        let deposit_8 := add(deposit_4, deposit_0)
                        if lt(deposit_8, deposit_4) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        sstore(0, deposit_8)
                        let deposit_9 := add(deposit_6, deposit_5)
                        if lt(deposit_9, deposit_6) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        sstore(1, deposit_9)
                        mstore(0, deposit_2)
                        mstore(32, 2)
                        let deposit_10 := sload(keccak256(0, 64))
                        let deposit_11 := add(deposit_6, deposit_10)
                        if lt(deposit_11, deposit_6) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        mstore(0, deposit_2)
                        mstore(32, 2)
                        sstore(keccak256(0, 64), deposit_11)
                        mstore(128, deposit_2)
                        mstore(160, deposit_0)
                        mstore(192, deposit_6)
                        log1(128, 96, 65375163721362069710668505494972926144572850546638504720594393917789416593941)
                        mstore(128, deposit_6)
                        return(128, 32)
                    }
                }
            }
            case 773487949 { // withdraw(uint256)
                {
                    if lt(calldatasize(), 36) {
                        revert(0, 0)
                    }
                }
                {
                    let withdraw_0 := calldataload(4)
                    let withdraw_1 := sload(3)
                    if iszero(eq(withdraw_1, 0)) {
                        mstore(128, shl(224, 2659711688))
                        revert(128, 4)
                    }
                    if iszero(lt(0, withdraw_0)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    let withdraw_2 := caller()
                    mstore(0, withdraw_2)
                    mstore(32, 2)
                    let withdraw_3 := sload(keccak256(0, 64))
                    if iszero(iszero(lt(withdraw_3, withdraw_0))) {
                        mstore(128, shl(224, 966354279))
                        revert(128, 4)
                    }
                    let withdraw_4 := sload(0)
                    let withdraw_5 := sload(1)
                    if iszero(withdraw_5) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 18)
                        revert(128, 36)
                    }
                    let withdraw_6 := mul(withdraw_4, withdraw_0)
                    if iszero(or(iszero(withdraw_4), eq(div(withdraw_6, withdraw_4), withdraw_0))) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    withdraw_6 := div(withdraw_6, withdraw_5)
                    if iszero(lt(0, withdraw_6)) {
                        mstore(128, shl(224, 853111260))
                        revert(128, 4)
                    }
                    if lt(withdraw_3, withdraw_0) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let withdraw_7 := sub(withdraw_3, withdraw_0)
                    mstore(0, withdraw_2)
                    mstore(32, 2)
                    sstore(keccak256(0, 64), withdraw_7)
                    if lt(withdraw_5, withdraw_0) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let withdraw_8 := sub(withdraw_5, withdraw_0)
                    sstore(1, withdraw_8)
                    if lt(withdraw_4, withdraw_6) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let withdraw_9 := sub(withdraw_4, withdraw_6)
                    sstore(0, withdraw_9)
                    let withdraw_10 := 0
                    {
                        let withdraw__tok_10 := sload(5)
                        mstore(128, shl(224, 2835717307))
                        mstore(132, withdraw_2)
                        mstore(164, withdraw_6)
                        let withdraw__ok_10 := call(1000000, withdraw__tok_10, 0, 128, 68, 128, 32)
                        if iszero(withdraw__ok_10) {
                            revert(0, 0)
                        }
                        if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                            revert(0, 0)
                        }
                        withdraw_10 := 1
                    }
                    if iszero(iszero(eq(withdraw_10, 0))) {
                        mstore(128, shl(224, 2428038168))
                        revert(128, 4)
                    }
                    mstore(128, withdraw_2)
                    mstore(160, withdraw_6)
                    mstore(192, withdraw_0)
                    log1(128, 96, 109675089620094772280264318389135030480951249233487863733592477092391202960744)
                    mstore(128, withdraw_6)
                    return(128, 32)
                }
            }
            case 4018876663 { // previewDeposit(uint256)
                {
                    if lt(calldatasize(), 36) {
                        revert(0, 0)
                    }
                }
                {
                    let previewDeposit_0 := calldataload(4)
                    let previewDeposit_1 := sload(0)
                    let previewDeposit_2 := sload(1)
                    switch eq(previewDeposit_2, 0)
                    case 0 {
                        if iszero(previewDeposit_1) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 18)
                            revert(128, 36)
                        }
                        let previewDeposit_3 := mul(previewDeposit_2, previewDeposit_0)
                        if iszero(or(iszero(previewDeposit_2), eq(div(previewDeposit_3, previewDeposit_2), previewDeposit_0))) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        previewDeposit_3 := div(previewDeposit_3, previewDeposit_1)
                        mstore(128, previewDeposit_3)
                        return(128, 32)
                    }
                    default {
                        mstore(128, previewDeposit_0)
                        return(128, 32)
                    }
                }
            }
            case 1289409798 { // previewRedeem(uint256)
                {
                    if lt(calldatasize(), 36) {
                        revert(0, 0)
                    }
                }
                {
                    let previewRedeem_0 := calldataload(4)
                    let previewRedeem_1 := sload(0)
                    let previewRedeem_2 := sload(1)
                    if iszero(previewRedeem_2) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 18)
                        revert(128, 36)
                    }
                    let previewRedeem_3 := mul(previewRedeem_1, previewRedeem_0)
                    if iszero(or(iszero(previewRedeem_1), eq(div(previewRedeem_3, previewRedeem_1), previewRedeem_0))) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    previewRedeem_3 := div(previewRedeem_3, previewRedeem_2)
                    mstore(128, previewRedeem_3)
                    return(128, 32)
                }
            }
            case 2220280665 { // pause()
                {
                    if lt(calldatasize(), 4) {
                        revert(0, 0)
                    }
                }
                {
                    let pause_0 := caller()
                    let pause_1 := sload(4)
                    if iszero(eq(pause_0, pause_1)) {
                        mstore(128, shl(224, 818771057))
                        revert(128, 4)
                    }
                    sstore(3, 1)
                    log1(128, 0, 71705685273638215938037424758762834198033328358739847630456454391896748713810)
                    stop()
                }
            }
            case 1061922874 { // unpause()
                {
                    if lt(calldatasize(), 4) {
                        revert(0, 0)
                    }
                }
                {
                    let unpause_0 := caller()
                    let unpause_1 := sload(4)
                    if iszero(eq(unpause_0, unpause_1)) {
                        mstore(128, shl(224, 818771057))
                        revert(128, 4)
                    }
                    sstore(3, 0)
                    log1(128, 0, 74347654508366659082915455395078899690017902693342448922959761368987215161651)
                    stop()
                }
            }
            case 1742577938 { // paused?()
                {
                    if lt(calldatasize(), 4) {
                        revert(0, 0)
                    }
                }
                {
                    let paused?_0 := sload(3)
                    mstore(128, paused?_0)
                    return(128, 32)
                }
            }
            case 826074471 { // decimals()
                {
                    if lt(calldatasize(), 4) {
                        revert(0, 0)
                    }
                }
                {
                    let decimals_0 := sload(6)
                    mstore(128, decimals_0)
                    return(128, 32)
                }
            }
            default {
                revert(0, 0)
            }
        }
    }
}
