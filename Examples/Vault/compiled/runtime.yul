// selector → function  (hex and decimal; `switch` cases print decimal)
//   0xb6b55f25  (3065339685)  deposit(uint256)
//   0x2e1a7d4d  (773487949)  withdraw(uint256)
//   0xef8b30f7  (4018876663)  previewDeposit(uint256)
//   0x4cdad506  (1289409798)  previewRedeem(uint256)
//   0x8456cb59  (2220280665)  pause()
//   0x3f4ba83a  (1061922874)  unpause()
//   0xb187bd26  (2978463014)  isPaused()

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
    case 3065339685 { // deposit(uint256)
        {
            if lt(calldatasize(), 36) {
                revert(0, 0)
            }
        }
        tstore(0, 1)
        {
            let deposit_0 := calldataload(4)
            let deposit_1 := sload(2)
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
            let deposit_5 := 0
            {
                mstore(128, shl(224, 1889567281))
                mstore(132, deposit_3)
                let deposit__ok_5 := staticcall(1000000, deposit_4, 128, 36, 128, 32)
                if iszero(deposit__ok_5) {
                    revert(0, 0)
                }
                if iszero(and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64))) {
                    revert(0, 0)
                }
                deposit_5 := mload(128)
            }
            let deposit_6 := sload(3)
            switch eq(deposit_6, 0)
            case 0 {
                if iszero(deposit_5) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 18)
                    revert(128, 36)
                }
                let deposit_7 := mul(deposit_6, deposit_0)
                if iszero(or(iszero(deposit_6), eq(div(deposit_7, deposit_6), deposit_0))) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                deposit_7 := div(deposit_7, deposit_5)
                if iszero(lt(0, deposit_7)) {
                    mstore(128, shl(224, 2551308487))
                    revert(128, 4)
                }
                let deposit_8 := add(deposit_6, deposit_7)
                if lt(deposit_8, deposit_6) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                sstore(3, deposit_8)
                mstore(0, deposit_2)
                mstore(32, 4)
                let deposit_9 := sload(keccak256(0, 64))
                let deposit_10 := add(deposit_9, deposit_7)
                if lt(deposit_10, deposit_9) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                mstore(0, deposit_2)
                mstore(32, 4)
                sstore(keccak256(0, 64), deposit_10)
                let deposit_11 := 0
                {
                    mstore(128, shl(224, 599290589))
                    mstore(132, deposit_2)
                    mstore(164, deposit_3)
                    mstore(196, deposit_0)
                    let deposit__ok_11 := call(1000000, deposit_4, 0, 128, 100, 128, 32)
                    if iszero(deposit__ok_11) {
                        revert(0, 0)
                    }
                    if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                        revert(0, 0)
                    }
                    deposit_11 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
                }
                if iszero(eq(deposit_11, 1)) {
                    mstore(128, shl(224, 2428038168))
                    revert(128, 4)
                }
                mstore(128, deposit_2)
                mstore(160, deposit_0)
                mstore(192, deposit_7)
                log1(128, 96, 65375163721362069710668505494972926144572850546638504720594393917789416593941)
                tstore(0, 0)
                mstore(128, deposit_7)
                return(128, 32)
            }
            default {
                let deposit_7 := deposit_0
                if iszero(lt(0, deposit_7)) {
                    mstore(128, shl(224, 2551308487))
                    revert(128, 4)
                }
                let deposit_8 := add(deposit_6, deposit_7)
                if lt(deposit_8, deposit_6) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                sstore(3, deposit_8)
                mstore(0, deposit_2)
                mstore(32, 4)
                let deposit_9 := sload(keccak256(0, 64))
                let deposit_10 := add(deposit_9, deposit_7)
                if lt(deposit_10, deposit_9) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                mstore(0, deposit_2)
                mstore(32, 4)
                sstore(keccak256(0, 64), deposit_10)
                let deposit_11 := 0
                {
                    mstore(128, shl(224, 599290589))
                    mstore(132, deposit_2)
                    mstore(164, deposit_3)
                    mstore(196, deposit_0)
                    let deposit__ok_11 := call(1000000, deposit_4, 0, 128, 100, 128, 32)
                    if iszero(deposit__ok_11) {
                        revert(0, 0)
                    }
                    if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                        revert(0, 0)
                    }
                    deposit_11 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
                }
                if iszero(eq(deposit_11, 1)) {
                    mstore(128, shl(224, 2428038168))
                    revert(128, 4)
                }
                mstore(128, deposit_2)
                mstore(160, deposit_0)
                mstore(192, deposit_7)
                log1(128, 96, 65375163721362069710668505494972926144572850546638504720594393917789416593941)
                tstore(0, 0)
                mstore(128, deposit_7)
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
        tstore(0, 1)
        {
            let withdraw_0 := calldataload(4)
            let withdraw_1 := sload(2)
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
            mstore(32, 4)
            let withdraw_3 := sload(keccak256(0, 64))
            if iszero(iszero(lt(withdraw_3, withdraw_0))) {
                mstore(128, shl(224, 966354279))
                revert(128, 4)
            }
            let withdraw_4 := address()
            let withdraw_5 := sload(0)
            let withdraw_6 := 0
            {
                mstore(128, shl(224, 1889567281))
                mstore(132, withdraw_4)
                let withdraw__ok_6 := staticcall(1000000, withdraw_5, 128, 36, 128, 32)
                if iszero(withdraw__ok_6) {
                    revert(0, 0)
                }
                if iszero(and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64))) {
                    revert(0, 0)
                }
                withdraw_6 := mload(128)
            }
            let withdraw_7 := sload(3)
            if iszero(withdraw_7) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 18)
                revert(128, 36)
            }
            let withdraw_8 := mul(withdraw_6, withdraw_0)
            if iszero(or(iszero(withdraw_6), eq(div(withdraw_8, withdraw_6), withdraw_0))) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            withdraw_8 := div(withdraw_8, withdraw_7)
            if iszero(lt(0, withdraw_8)) {
                mstore(128, shl(224, 853111260))
                revert(128, 4)
            }
            if lt(withdraw_3, withdraw_0) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            let withdraw_9 := sub(withdraw_3, withdraw_0)
            mstore(0, withdraw_2)
            mstore(32, 4)
            sstore(keccak256(0, 64), withdraw_9)
            if lt(withdraw_7, withdraw_0) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            let withdraw_10 := sub(withdraw_7, withdraw_0)
            sstore(3, withdraw_10)
            let withdraw_11 := 0
            {
                mstore(128, shl(224, 2835717307))
                mstore(132, withdraw_2)
                mstore(164, withdraw_8)
                let withdraw__ok_11 := call(1000000, withdraw_5, 0, 128, 68, 128, 32)
                if iszero(withdraw__ok_11) {
                    revert(0, 0)
                }
                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                    revert(0, 0)
                }
                withdraw_11 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
            }
            if iszero(eq(withdraw_11, 1)) {
                mstore(128, shl(224, 2428038168))
                revert(128, 4)
            }
            mstore(128, withdraw_2)
            mstore(160, withdraw_8)
            mstore(192, withdraw_0)
            log1(128, 96, 109675089620094772280264318389135030480951249233487863733592477092391202960744)
            tstore(0, 0)
            mstore(128, withdraw_8)
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
            let previewDeposit_1 := address()
            let previewDeposit_2 := sload(0)
            let previewDeposit_3 := 0
            {
                mstore(128, shl(224, 1889567281))
                mstore(132, previewDeposit_1)
                let previewDeposit__ok_3 := staticcall(1000000, previewDeposit_2, 128, 36, 128, 32)
                if iszero(previewDeposit__ok_3) {
                    revert(0, 0)
                }
                if iszero(and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64))) {
                    revert(0, 0)
                }
                previewDeposit_3 := mload(128)
            }
            let previewDeposit_4 := sload(3)
            switch eq(previewDeposit_4, 0)
            case 0 {
                if iszero(previewDeposit_3) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 18)
                    revert(128, 36)
                }
                let previewDeposit_5 := mul(previewDeposit_4, previewDeposit_0)
                if iszero(or(iszero(previewDeposit_4), eq(div(previewDeposit_5, previewDeposit_4), previewDeposit_0))) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                previewDeposit_5 := div(previewDeposit_5, previewDeposit_3)
                mstore(128, previewDeposit_5)
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
            let previewRedeem_1 := address()
            let previewRedeem_2 := sload(0)
            let previewRedeem_3 := 0
            {
                mstore(128, shl(224, 1889567281))
                mstore(132, previewRedeem_1)
                let previewRedeem__ok_3 := staticcall(1000000, previewRedeem_2, 128, 36, 128, 32)
                if iszero(previewRedeem__ok_3) {
                    revert(0, 0)
                }
                if iszero(and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64))) {
                    revert(0, 0)
                }
                previewRedeem_3 := mload(128)
            }
            let previewRedeem_4 := sload(3)
            if iszero(previewRedeem_4) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 18)
                revert(128, 36)
            }
            let previewRedeem_5 := mul(previewRedeem_3, previewRedeem_0)
            if iszero(or(iszero(previewRedeem_3), eq(div(previewRedeem_5, previewRedeem_3), previewRedeem_0))) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            previewRedeem_5 := div(previewRedeem_5, previewRedeem_4)
            mstore(128, previewRedeem_5)
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
            let pause_1 := sload(1)
            if iszero(eq(pause_0, pause_1)) {
                mstore(128, shl(224, 818771057))
                revert(128, 4)
            }
            sstore(2, 1)
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
            let unpause_1 := sload(1)
            if iszero(eq(unpause_0, unpause_1)) {
                mstore(128, shl(224, 818771057))
                revert(128, 4)
            }
            sstore(2, 0)
            log1(128, 0, 74347654508366659082915455395078899690017902693342448922959761368987215161651)
            stop()
        }
    }
    case 2978463014 { // isPaused()
        {
            if lt(calldatasize(), 4) {
                revert(0, 0)
            }
        }
        {
            let isPaused_0 := sload(2)
            mstore(128, isPaused_0)
            return(128, 32)
        }
    }
    default {
        revert(0, 0)
    }
}
