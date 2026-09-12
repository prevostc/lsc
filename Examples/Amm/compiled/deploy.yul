// selector → function  (hex and decimal; `switch` cases print decimal)
//   0x9cd441da  (2631156186)  addLiquidity(uint256,uint256)
//   0x9c8f9f23  (2626658083)  removeLiquidity(uint256)
//   0x2b1087f0  (722503664)  swap0for1(uint256,uint256)
//   0x21d2da23  (567466531)  swap1for0(uint256,uint256)
//   0x0902f1ac  (151187884)  getReserves()
//   0xf5eb42dc  (4125835996)  sharesOf(address)
//   0x19d4b175  (433369461)  quote0for1(uint256)

object "Amm" {
    code {
        codecopy(128, sub(codesize(), 64), 64)
        let constructor_0 := mload(128)
        let constructor_1 := mload(160)
        if iszero(iszero(eq(constructor_0, constructor_1))) {
            mstore(128, shl(224, 538662922))
            revert(128, 4)
        }
        sstore(0, constructor_0)
        sstore(1, constructor_1)
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
            case 2631156186 { // addLiquidity(uint256,uint256)
                {
                    if lt(calldatasize(), 68) {
                        revert(0, 0)
                    }
                }
                {
                    let addLiquidity_0 := calldataload(4)
                    let addLiquidity_1 := calldataload(36)
                    if iszero(lt(0, addLiquidity_0)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    if iszero(lt(0, addLiquidity_1)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    let addLiquidity_2 := caller()
                    let addLiquidity_3 := address()
                    let addLiquidity_4 := sload(2)
                    let addLiquidity_5 := sload(3)
                    let addLiquidity_6 := sload(4)
                    switch eq(addLiquidity_6, 0)
                    case 0 {
                        if iszero(lt(0, addLiquidity_4)) {
                            mstore(128, shl(224, 4099277827))
                            revert(128, 4)
                        }
                        if iszero(lt(0, addLiquidity_5)) {
                            mstore(128, shl(224, 4099277827))
                            revert(128, 4)
                        }
                        if iszero(addLiquidity_4) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 18)
                            revert(128, 36)
                        }
                        let addLiquidity_7 := mul(addLiquidity_6, addLiquidity_0)
                        if iszero(or(iszero(addLiquidity_6), eq(div(addLiquidity_7, addLiquidity_6), addLiquidity_0))) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        addLiquidity_7 := div(addLiquidity_7, addLiquidity_4)
                        if iszero(addLiquidity_5) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 18)
                            revert(128, 36)
                        }
                        let addLiquidity_8 := mul(addLiquidity_6, addLiquidity_1)
                        if iszero(or(iszero(addLiquidity_6), eq(div(addLiquidity_8, addLiquidity_6), addLiquidity_1))) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        addLiquidity_8 := div(addLiquidity_8, addLiquidity_5)
                        switch iszero(lt(addLiquidity_8, addLiquidity_7))
                        case 0 {
                            let addLiquidity_9 := addLiquidity_8
                            if iszero(lt(0, addLiquidity_9)) {
                                mstore(128, shl(224, 2551308487))
                                revert(128, 4)
                            }
                            let addLiquidity_10 := add(addLiquidity_4, addLiquidity_0)
                            if lt(addLiquidity_10, addLiquidity_4) {
                                mstore(128, shl(224, 1313373041))
                                mstore(132, 17)
                                revert(128, 36)
                            }
                            sstore(2, addLiquidity_10)
                            let addLiquidity_11 := add(addLiquidity_5, addLiquidity_1)
                            if lt(addLiquidity_11, addLiquidity_5) {
                                mstore(128, shl(224, 1313373041))
                                mstore(132, 17)
                                revert(128, 36)
                            }
                            sstore(3, addLiquidity_11)
                            let addLiquidity_12 := add(addLiquidity_9, addLiquidity_6)
                            if lt(addLiquidity_12, addLiquidity_9) {
                                mstore(128, shl(224, 1313373041))
                                mstore(132, 17)
                                revert(128, 36)
                            }
                            sstore(4, addLiquidity_12)
                            mstore(0, addLiquidity_2)
                            mstore(32, 5)
                            let addLiquidity_13 := sload(keccak256(0, 64))
                            let addLiquidity_14 := add(addLiquidity_9, addLiquidity_13)
                            if lt(addLiquidity_14, addLiquidity_9) {
                                mstore(128, shl(224, 1313373041))
                                mstore(132, 17)
                                revert(128, 36)
                            }
                            mstore(0, addLiquidity_2)
                            mstore(32, 5)
                            sstore(keccak256(0, 64), addLiquidity_14)
                            let addLiquidity_15 := 0
                            {
                                let addLiquidity__tok_15 := sload(0)
                                mstore(128, shl(224, 599290589))
                                mstore(132, addLiquidity_2)
                                mstore(164, addLiquidity_3)
                                mstore(196, addLiquidity_0)
                                let addLiquidity__ok_15 := call(1000000, addLiquidity__tok_15, 0, 128, 100, 128, 32)
                                if iszero(addLiquidity__ok_15) {
                                    revert(0, 0)
                                }
                                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                                    revert(0, 0)
                                }
                                addLiquidity_15 := 1
                            }
                            if iszero(iszero(eq(addLiquidity_15, 0))) {
                                mstore(128, shl(224, 2428038168))
                                revert(128, 4)
                            }
                            let addLiquidity_16 := 0
                            {
                                let addLiquidity__tok_16 := sload(1)
                                mstore(128, shl(224, 599290589))
                                mstore(132, addLiquidity_2)
                                mstore(164, addLiquidity_3)
                                mstore(196, addLiquidity_1)
                                let addLiquidity__ok_16 := call(1000000, addLiquidity__tok_16, 0, 128, 100, 128, 32)
                                if iszero(addLiquidity__ok_16) {
                                    revert(0, 0)
                                }
                                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                                    revert(0, 0)
                                }
                                addLiquidity_16 := 1
                            }
                            if iszero(iszero(eq(addLiquidity_16, 0))) {
                                mstore(128, shl(224, 2428038168))
                                revert(128, 4)
                            }
                            mstore(128, addLiquidity_2)
                            mstore(160, addLiquidity_0)
                            mstore(192, addLiquidity_1)
                            mstore(224, addLiquidity_9)
                            log1(128, 128, 86256647852634439136012048383694880642795699201302061824315076091651743641550)
                            mstore(128, addLiquidity_9)
                            return(128, 32)
                        }
                        default {
                            let addLiquidity_9 := addLiquidity_7
                            if iszero(lt(0, addLiquidity_9)) {
                                mstore(128, shl(224, 2551308487))
                                revert(128, 4)
                            }
                            let addLiquidity_10 := add(addLiquidity_4, addLiquidity_0)
                            if lt(addLiquidity_10, addLiquidity_4) {
                                mstore(128, shl(224, 1313373041))
                                mstore(132, 17)
                                revert(128, 36)
                            }
                            sstore(2, addLiquidity_10)
                            let addLiquidity_11 := add(addLiquidity_5, addLiquidity_1)
                            if lt(addLiquidity_11, addLiquidity_5) {
                                mstore(128, shl(224, 1313373041))
                                mstore(132, 17)
                                revert(128, 36)
                            }
                            sstore(3, addLiquidity_11)
                            let addLiquidity_12 := add(addLiquidity_9, addLiquidity_6)
                            if lt(addLiquidity_12, addLiquidity_9) {
                                mstore(128, shl(224, 1313373041))
                                mstore(132, 17)
                                revert(128, 36)
                            }
                            sstore(4, addLiquidity_12)
                            mstore(0, addLiquidity_2)
                            mstore(32, 5)
                            let addLiquidity_13 := sload(keccak256(0, 64))
                            let addLiquidity_14 := add(addLiquidity_9, addLiquidity_13)
                            if lt(addLiquidity_14, addLiquidity_9) {
                                mstore(128, shl(224, 1313373041))
                                mstore(132, 17)
                                revert(128, 36)
                            }
                            mstore(0, addLiquidity_2)
                            mstore(32, 5)
                            sstore(keccak256(0, 64), addLiquidity_14)
                            let addLiquidity_15 := 0
                            {
                                let addLiquidity__tok_15 := sload(0)
                                mstore(128, shl(224, 599290589))
                                mstore(132, addLiquidity_2)
                                mstore(164, addLiquidity_3)
                                mstore(196, addLiquidity_0)
                                let addLiquidity__ok_15 := call(1000000, addLiquidity__tok_15, 0, 128, 100, 128, 32)
                                if iszero(addLiquidity__ok_15) {
                                    revert(0, 0)
                                }
                                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                                    revert(0, 0)
                                }
                                addLiquidity_15 := 1
                            }
                            if iszero(iszero(eq(addLiquidity_15, 0))) {
                                mstore(128, shl(224, 2428038168))
                                revert(128, 4)
                            }
                            let addLiquidity_16 := 0
                            {
                                let addLiquidity__tok_16 := sload(1)
                                mstore(128, shl(224, 599290589))
                                mstore(132, addLiquidity_2)
                                mstore(164, addLiquidity_3)
                                mstore(196, addLiquidity_1)
                                let addLiquidity__ok_16 := call(1000000, addLiquidity__tok_16, 0, 128, 100, 128, 32)
                                if iszero(addLiquidity__ok_16) {
                                    revert(0, 0)
                                }
                                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                                    revert(0, 0)
                                }
                                addLiquidity_16 := 1
                            }
                            if iszero(iszero(eq(addLiquidity_16, 0))) {
                                mstore(128, shl(224, 2428038168))
                                revert(128, 4)
                            }
                            mstore(128, addLiquidity_2)
                            mstore(160, addLiquidity_0)
                            mstore(192, addLiquidity_1)
                            mstore(224, addLiquidity_9)
                            log1(128, 128, 86256647852634439136012048383694880642795699201302061824315076091651743641550)
                            mstore(128, addLiquidity_9)
                            return(128, 32)
                        }
                    }
                    default {
                        let addLiquidity_7 := addLiquidity_0
                        if iszero(lt(0, addLiquidity_7)) {
                            mstore(128, shl(224, 2551308487))
                            revert(128, 4)
                        }
                        let addLiquidity_8 := add(addLiquidity_4, addLiquidity_0)
                        if lt(addLiquidity_8, addLiquidity_4) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        sstore(2, addLiquidity_8)
                        let addLiquidity_9 := add(addLiquidity_5, addLiquidity_1)
                        if lt(addLiquidity_9, addLiquidity_5) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        sstore(3, addLiquidity_9)
                        let addLiquidity_10 := add(addLiquidity_7, addLiquidity_6)
                        if lt(addLiquidity_10, addLiquidity_7) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        sstore(4, addLiquidity_10)
                        mstore(0, addLiquidity_2)
                        mstore(32, 5)
                        let addLiquidity_11 := sload(keccak256(0, 64))
                        let addLiquidity_12 := add(addLiquidity_7, addLiquidity_11)
                        if lt(addLiquidity_12, addLiquidity_7) {
                            mstore(128, shl(224, 1313373041))
                            mstore(132, 17)
                            revert(128, 36)
                        }
                        mstore(0, addLiquidity_2)
                        mstore(32, 5)
                        sstore(keccak256(0, 64), addLiquidity_12)
                        let addLiquidity_13 := 0
                        {
                            let addLiquidity__tok_13 := sload(0)
                            mstore(128, shl(224, 599290589))
                            mstore(132, addLiquidity_2)
                            mstore(164, addLiquidity_3)
                            mstore(196, addLiquidity_0)
                            let addLiquidity__ok_13 := call(1000000, addLiquidity__tok_13, 0, 128, 100, 128, 32)
                            if iszero(addLiquidity__ok_13) {
                                revert(0, 0)
                            }
                            if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                                revert(0, 0)
                            }
                            addLiquidity_13 := 1
                        }
                        if iszero(iszero(eq(addLiquidity_13, 0))) {
                            mstore(128, shl(224, 2428038168))
                            revert(128, 4)
                        }
                        let addLiquidity_14 := 0
                        {
                            let addLiquidity__tok_14 := sload(1)
                            mstore(128, shl(224, 599290589))
                            mstore(132, addLiquidity_2)
                            mstore(164, addLiquidity_3)
                            mstore(196, addLiquidity_1)
                            let addLiquidity__ok_14 := call(1000000, addLiquidity__tok_14, 0, 128, 100, 128, 32)
                            if iszero(addLiquidity__ok_14) {
                                revert(0, 0)
                            }
                            if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                                revert(0, 0)
                            }
                            addLiquidity_14 := 1
                        }
                        if iszero(iszero(eq(addLiquidity_14, 0))) {
                            mstore(128, shl(224, 2428038168))
                            revert(128, 4)
                        }
                        mstore(128, addLiquidity_2)
                        mstore(160, addLiquidity_0)
                        mstore(192, addLiquidity_1)
                        mstore(224, addLiquidity_7)
                        log1(128, 128, 86256647852634439136012048383694880642795699201302061824315076091651743641550)
                        mstore(128, addLiquidity_7)
                        return(128, 32)
                    }
                }
            }
            case 2626658083 { // removeLiquidity(uint256)
                {
                    if lt(calldatasize(), 36) {
                        revert(0, 0)
                    }
                }
                {
                    let removeLiquidity_0 := calldataload(4)
                    if iszero(lt(0, removeLiquidity_0)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    let removeLiquidity_1 := caller()
                    mstore(0, removeLiquidity_1)
                    mstore(32, 5)
                    let removeLiquidity_2 := sload(keccak256(0, 64))
                    if iszero(iszero(lt(removeLiquidity_2, removeLiquidity_0))) {
                        mstore(128, shl(224, 966354279))
                        revert(128, 4)
                    }
                    let removeLiquidity_3 := sload(2)
                    let removeLiquidity_4 := sload(3)
                    let removeLiquidity_5 := sload(4)
                    if iszero(lt(0, removeLiquidity_5)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    if iszero(removeLiquidity_5) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 18)
                        revert(128, 36)
                    }
                    let removeLiquidity_6 := mul(removeLiquidity_3, removeLiquidity_0)
                    if iszero(or(iszero(removeLiquidity_3), eq(div(removeLiquidity_6, removeLiquidity_3), removeLiquidity_0))) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    removeLiquidity_6 := div(removeLiquidity_6, removeLiquidity_5)
                    if iszero(removeLiquidity_5) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 18)
                        revert(128, 36)
                    }
                    let removeLiquidity_7 := mul(removeLiquidity_4, removeLiquidity_0)
                    if iszero(or(iszero(removeLiquidity_4), eq(div(removeLiquidity_7, removeLiquidity_4), removeLiquidity_0))) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    removeLiquidity_7 := div(removeLiquidity_7, removeLiquidity_5)
                    if iszero(lt(0, removeLiquidity_6)) {
                        mstore(128, shl(224, 276346163))
                        revert(128, 4)
                    }
                    if iszero(lt(0, removeLiquidity_7)) {
                        mstore(128, shl(224, 276346163))
                        revert(128, 4)
                    }
                    if lt(removeLiquidity_2, removeLiquidity_0) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let removeLiquidity_8 := sub(removeLiquidity_2, removeLiquidity_0)
                    mstore(0, removeLiquidity_1)
                    mstore(32, 5)
                    sstore(keccak256(0, 64), removeLiquidity_8)
                    if lt(removeLiquidity_5, removeLiquidity_0) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let removeLiquidity_9 := sub(removeLiquidity_5, removeLiquidity_0)
                    sstore(4, removeLiquidity_9)
                    if lt(removeLiquidity_3, removeLiquidity_6) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let removeLiquidity_10 := sub(removeLiquidity_3, removeLiquidity_6)
                    sstore(2, removeLiquidity_10)
                    if lt(removeLiquidity_4, removeLiquidity_7) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let removeLiquidity_11 := sub(removeLiquidity_4, removeLiquidity_7)
                    sstore(3, removeLiquidity_11)
                    let removeLiquidity_12 := 0
                    {
                        let removeLiquidity__tok_12 := sload(0)
                        mstore(128, shl(224, 2835717307))
                        mstore(132, removeLiquidity_1)
                        mstore(164, removeLiquidity_6)
                        let removeLiquidity__ok_12 := call(1000000, removeLiquidity__tok_12, 0, 128, 68, 128, 32)
                        if iszero(removeLiquidity__ok_12) {
                            revert(0, 0)
                        }
                        if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                            revert(0, 0)
                        }
                        removeLiquidity_12 := 1
                    }
                    if iszero(iszero(eq(removeLiquidity_12, 0))) {
                        mstore(128, shl(224, 2428038168))
                        revert(128, 4)
                    }
                    let removeLiquidity_13 := 0
                    {
                        let removeLiquidity__tok_13 := sload(1)
                        mstore(128, shl(224, 2835717307))
                        mstore(132, removeLiquidity_1)
                        mstore(164, removeLiquidity_7)
                        let removeLiquidity__ok_13 := call(1000000, removeLiquidity__tok_13, 0, 128, 68, 128, 32)
                        if iszero(removeLiquidity__ok_13) {
                            revert(0, 0)
                        }
                        if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                            revert(0, 0)
                        }
                        removeLiquidity_13 := 1
                    }
                    if iszero(iszero(eq(removeLiquidity_13, 0))) {
                        mstore(128, shl(224, 2428038168))
                        revert(128, 4)
                    }
                    mstore(128, removeLiquidity_1)
                    mstore(160, removeLiquidity_6)
                    mstore(192, removeLiquidity_7)
                    mstore(224, removeLiquidity_0)
                    log1(128, 128, 40601487888975922259554448828720518987931677697835248007167516320394709135098)
                    mstore(128, removeLiquidity_6)
                    mstore(160, removeLiquidity_7)
                    return(128, 64)
                }
            }
            case 722503664 { // swap0for1(uint256,uint256)
                {
                    if lt(calldatasize(), 68) {
                        revert(0, 0)
                    }
                }
                {
                    let swap0for1_0 := calldataload(4)
                    let swap0for1_1 := calldataload(36)
                    if iszero(lt(0, swap0for1_0)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    let swap0for1_2 := sload(2)
                    let swap0for1_3 := sload(3)
                    if iszero(lt(0, swap0for1_2)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    if iszero(lt(0, swap0for1_3)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    let swap0for1_4 := add(swap0for1_2, swap0for1_0)
                    if lt(swap0for1_4, swap0for1_2) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    if iszero(swap0for1_4) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 18)
                        revert(128, 36)
                    }
                    let swap0for1_5 := mul(swap0for1_3, swap0for1_0)
                    if iszero(or(iszero(swap0for1_3), eq(div(swap0for1_5, swap0for1_3), swap0for1_0))) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    swap0for1_5 := div(swap0for1_5, swap0for1_4)
                    if iszero(iszero(lt(swap0for1_5, swap0for1_1))) {
                        mstore(128, shl(224, 3139990979))
                        revert(128, 4)
                    }
                    if iszero(lt(0, swap0for1_5)) {
                        mstore(128, shl(224, 276346163))
                        revert(128, 4)
                    }
                    let swap0for1_6 := add(swap0for1_2, swap0for1_0)
                    if lt(swap0for1_6, swap0for1_2) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    sstore(2, swap0for1_6)
                    if lt(swap0for1_3, swap0for1_5) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let swap0for1_7 := sub(swap0for1_3, swap0for1_5)
                    sstore(3, swap0for1_7)
                    let swap0for1_8 := caller()
                    let swap0for1_9 := address()
                    let swap0for1_10 := 0
                    {
                        let swap0for1__tok_10 := sload(0)
                        mstore(128, shl(224, 599290589))
                        mstore(132, swap0for1_8)
                        mstore(164, swap0for1_9)
                        mstore(196, swap0for1_0)
                        let swap0for1__ok_10 := call(1000000, swap0for1__tok_10, 0, 128, 100, 128, 32)
                        if iszero(swap0for1__ok_10) {
                            revert(0, 0)
                        }
                        if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                            revert(0, 0)
                        }
                        swap0for1_10 := 1
                    }
                    if iszero(iszero(eq(swap0for1_10, 0))) {
                        mstore(128, shl(224, 2428038168))
                        revert(128, 4)
                    }
                    let swap0for1_11 := 0
                    {
                        let swap0for1__tok_11 := sload(1)
                        mstore(128, shl(224, 2835717307))
                        mstore(132, swap0for1_8)
                        mstore(164, swap0for1_5)
                        let swap0for1__ok_11 := call(1000000, swap0for1__tok_11, 0, 128, 68, 128, 32)
                        if iszero(swap0for1__ok_11) {
                            revert(0, 0)
                        }
                        if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                            revert(0, 0)
                        }
                        swap0for1_11 := 1
                    }
                    if iszero(iszero(eq(swap0for1_11, 0))) {
                        mstore(128, shl(224, 2428038168))
                        revert(128, 4)
                    }
                    mstore(128, swap0for1_8)
                    mstore(160, swap0for1_0)
                    mstore(192, swap0for1_5)
                    log1(128, 96, 17437238319937237281100397956711788736631309589920004552140586013878294093770)
                    mstore(128, swap0for1_5)
                    return(128, 32)
                }
            }
            case 567466531 { // swap1for0(uint256,uint256)
                {
                    if lt(calldatasize(), 68) {
                        revert(0, 0)
                    }
                }
                {
                    let swap1for0_0 := calldataload(4)
                    let swap1for0_1 := calldataload(36)
                    if iszero(lt(0, swap1for0_0)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    let swap1for0_2 := sload(2)
                    let swap1for0_3 := sload(3)
                    if iszero(lt(0, swap1for0_2)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    if iszero(lt(0, swap1for0_3)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    let swap1for0_4 := add(swap1for0_3, swap1for0_0)
                    if lt(swap1for0_4, swap1for0_3) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    if iszero(swap1for0_4) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 18)
                        revert(128, 36)
                    }
                    let swap1for0_5 := mul(swap1for0_2, swap1for0_0)
                    if iszero(or(iszero(swap1for0_2), eq(div(swap1for0_5, swap1for0_2), swap1for0_0))) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    swap1for0_5 := div(swap1for0_5, swap1for0_4)
                    if iszero(iszero(lt(swap1for0_5, swap1for0_1))) {
                        mstore(128, shl(224, 3139990979))
                        revert(128, 4)
                    }
                    if iszero(lt(0, swap1for0_5)) {
                        mstore(128, shl(224, 276346163))
                        revert(128, 4)
                    }
                    let swap1for0_6 := add(swap1for0_3, swap1for0_0)
                    if lt(swap1for0_6, swap1for0_3) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    sstore(3, swap1for0_6)
                    if lt(swap1for0_2, swap1for0_5) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let swap1for0_7 := sub(swap1for0_2, swap1for0_5)
                    sstore(2, swap1for0_7)
                    let swap1for0_8 := caller()
                    let swap1for0_9 := address()
                    let swap1for0_10 := 0
                    {
                        let swap1for0__tok_10 := sload(1)
                        mstore(128, shl(224, 599290589))
                        mstore(132, swap1for0_8)
                        mstore(164, swap1for0_9)
                        mstore(196, swap1for0_0)
                        let swap1for0__ok_10 := call(1000000, swap1for0__tok_10, 0, 128, 100, 128, 32)
                        if iszero(swap1for0__ok_10) {
                            revert(0, 0)
                        }
                        if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                            revert(0, 0)
                        }
                        swap1for0_10 := 1
                    }
                    if iszero(iszero(eq(swap1for0_10, 0))) {
                        mstore(128, shl(224, 2428038168))
                        revert(128, 4)
                    }
                    let swap1for0_11 := 0
                    {
                        let swap1for0__tok_11 := sload(0)
                        mstore(128, shl(224, 2835717307))
                        mstore(132, swap1for0_8)
                        mstore(164, swap1for0_5)
                        let swap1for0__ok_11 := call(1000000, swap1for0__tok_11, 0, 128, 68, 128, 32)
                        if iszero(swap1for0__ok_11) {
                            revert(0, 0)
                        }
                        if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(128), 1)))) {
                            revert(0, 0)
                        }
                        swap1for0_11 := 1
                    }
                    if iszero(iszero(eq(swap1for0_11, 0))) {
                        mstore(128, shl(224, 2428038168))
                        revert(128, 4)
                    }
                    mstore(128, swap1for0_8)
                    mstore(160, swap1for0_0)
                    mstore(192, swap1for0_5)
                    log1(128, 96, 106865371797876764641124053122323485270600095508620925271233383623886030425246)
                    mstore(128, swap1for0_5)
                    return(128, 32)
                }
            }
            case 151187884 { // getReserves()
                {
                    if lt(calldatasize(), 4) {
                        revert(0, 0)
                    }
                }
                {
                    let getReserves_0 := sload(2)
                    let getReserves_1 := sload(3)
                    mstore(128, getReserves_0)
                    mstore(160, getReserves_1)
                    return(128, 64)
                }
            }
            case 4125835996 { // sharesOf(address)
                {
                    if lt(calldatasize(), 36) {
                        revert(0, 0)
                    }
                }
                {
                    let sharesOf_0 := calldataload(4)
                    mstore(0, sharesOf_0)
                    mstore(32, 5)
                    let sharesOf_1 := sload(keccak256(0, 64))
                    mstore(128, sharesOf_1)
                    return(128, 32)
                }
            }
            case 433369461 { // quote0for1(uint256)
                {
                    if lt(calldatasize(), 36) {
                        revert(0, 0)
                    }
                }
                {
                    let quote0for1_0 := calldataload(4)
                    if iszero(lt(0, quote0for1_0)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    let quote0for1_1 := sload(2)
                    let quote0for1_2 := sload(3)
                    if iszero(lt(0, quote0for1_1)) {
                        mstore(128, shl(224, 4099277827))
                        revert(128, 4)
                    }
                    let quote0for1_3 := add(quote0for1_1, quote0for1_0)
                    if lt(quote0for1_3, quote0for1_1) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    if iszero(quote0for1_3) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 18)
                        revert(128, 36)
                    }
                    let quote0for1_4 := mul(quote0for1_2, quote0for1_0)
                    if iszero(or(iszero(quote0for1_2), eq(div(quote0for1_4, quote0for1_2), quote0for1_0))) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    quote0for1_4 := div(quote0for1_4, quote0for1_3)
                    mstore(128, quote0for1_4)
                    return(128, 32)
                }
            }
            default {
                revert(0, 0)
            }
        }
    }
}
