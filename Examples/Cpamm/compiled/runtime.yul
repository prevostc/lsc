// selector → function  (hex and decimal; `switch` cases print decimal)
//   0x9cd441da  (2631156186)  addLiquidity(uint256,uint256)
//   0x9c8f9f23  (2626658083)  removeLiquidity(uint256)
//   0x2b1087f0  (722503664)  swap0for1(uint256,uint256)
//   0x21d2da23  (567466531)  swap1for0(uint256,uint256)
//   0xce9c0bb7  (3466333111)  setProtocolShare(uint256)
//   0xf46901ed  (4100522477)  setFeeTo(address)
//   0xa1af5b9a  (2712624026)  collectProtocolFees()
//   0x0902f1ac  (151187884)  getReserves()
//   0xf5eb42dc  (4125835996)  sharesOf(address)
//   0x1ad8b03b  (450408507)  protocolFees()

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
    case 2631156186 { // addLiquidity(uint256,uint256)
        {
            if lt(calldatasize(), 68) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
        }
        tstore(0, 1)
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
            let addLiquidity_7 := 0
            {
                let addLiquidity__phi_7 := 0
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
                        addLiquidity__phi_7 := addLiquidity_9
                    }
                    default {
                        let addLiquidity_9 := addLiquidity_7
                        addLiquidity__phi_7 := addLiquidity_9
                    }
                }
                default {
                    let addLiquidity_7 := addLiquidity_0
                    if iszero(lt(1000, addLiquidity_7)) {
                        mstore(128, shl(224, 3142974759))
                        revert(128, 4)
                    }
                    mstore(0, 0)
                    mstore(32, 5)
                    let addLiquidity_8 := sload(keccak256(0, 64))
                    let addLiquidity_9 := add(addLiquidity_8, 1000)
                    if lt(addLiquidity_9, addLiquidity_8) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    mstore(0, 0)
                    mstore(32, 5)
                    sstore(keccak256(0, 64), addLiquidity_9)
                    let addLiquidity_10 := sload(4)
                    let addLiquidity_11 := add(addLiquidity_10, 1000)
                    if lt(addLiquidity_11, addLiquidity_10) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    sstore(4, addLiquidity_11)
                    if lt(addLiquidity_7, 1000) {
                        mstore(128, shl(224, 1313373041))
                        mstore(132, 17)
                        revert(128, 36)
                    }
                    let addLiquidity_12 := sub(addLiquidity_7, 1000)
                    addLiquidity__phi_7 := addLiquidity_12
                }
                addLiquidity_7 := addLiquidity__phi_7
            }
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
            mstore(0, addLiquidity_2)
            mstore(32, 5)
            let addLiquidity_10 := sload(keccak256(0, 64))
            let addLiquidity_11 := add(addLiquidity_10, addLiquidity_7)
            if lt(addLiquidity_11, addLiquidity_10) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            mstore(0, addLiquidity_2)
            mstore(32, 5)
            sstore(keccak256(0, 64), addLiquidity_11)
            let addLiquidity_12 := sload(4)
            let addLiquidity_13 := add(addLiquidity_12, addLiquidity_7)
            if lt(addLiquidity_13, addLiquidity_12) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            sstore(4, addLiquidity_13)
            let addLiquidity_14 := sload(0)
            let addLiquidity_15 := sload(1)
            let addLiquidity_16 := 0
            {
                mstore(128, shl(224, 599290589))
                mstore(132, addLiquidity_2)
                mstore(164, addLiquidity_3)
                mstore(196, addLiquidity_0)
                let addLiquidity__ok_16 := call(1000000, addLiquidity_14, 0, 128, 100, 128, 32)
                if iszero(addLiquidity__ok_16) {
                    revert(0, 0)
                }
                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                    revert(0, 0)
                }
                addLiquidity_16 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
            }
            if iszero(eq(addLiquidity_16, 1)) {
                mstore(128, shl(224, 2428038168))
                revert(128, 4)
            }
            let addLiquidity_17 := 0
            {
                mstore(128, shl(224, 599290589))
                mstore(132, addLiquidity_2)
                mstore(164, addLiquidity_3)
                mstore(196, addLiquidity_1)
                let addLiquidity__ok_17 := call(1000000, addLiquidity_15, 0, 128, 100, 128, 32)
                if iszero(addLiquidity__ok_17) {
                    revert(0, 0)
                }
                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                    revert(0, 0)
                }
                addLiquidity_17 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
            }
            if iszero(eq(addLiquidity_17, 1)) {
                mstore(128, shl(224, 2428038168))
                revert(128, 4)
            }
            mstore(128, addLiquidity_2)
            mstore(160, addLiquidity_0)
            mstore(192, addLiquidity_1)
            mstore(224, addLiquidity_7)
            log1(128, 128, 86256647852634439136012048383694880642795699201302061824315076091651743641550)
            tstore(0, 0)
            mstore(128, addLiquidity_7)
            return(128, 32)
        }
    }
    case 2626658083 { // removeLiquidity(uint256)
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
            let removeLiquidity_12 := sload(0)
            let removeLiquidity_13 := sload(1)
            let removeLiquidity_14 := 0
            {
                mstore(128, shl(224, 2835717307))
                mstore(132, removeLiquidity_1)
                mstore(164, removeLiquidity_6)
                let removeLiquidity__ok_14 := call(1000000, removeLiquidity_12, 0, 128, 68, 128, 32)
                if iszero(removeLiquidity__ok_14) {
                    revert(0, 0)
                }
                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                    revert(0, 0)
                }
                removeLiquidity_14 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
            }
            if iszero(eq(removeLiquidity_14, 1)) {
                mstore(128, shl(224, 2428038168))
                revert(128, 4)
            }
            let removeLiquidity_15 := 0
            {
                mstore(128, shl(224, 2835717307))
                mstore(132, removeLiquidity_1)
                mstore(164, removeLiquidity_7)
                let removeLiquidity__ok_15 := call(1000000, removeLiquidity_13, 0, 128, 68, 128, 32)
                if iszero(removeLiquidity__ok_15) {
                    revert(0, 0)
                }
                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                    revert(0, 0)
                }
                removeLiquidity_15 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
            }
            if iszero(eq(removeLiquidity_15, 1)) {
                mstore(128, shl(224, 2428038168))
                revert(128, 4)
            }
            mstore(128, removeLiquidity_1)
            mstore(160, removeLiquidity_6)
            mstore(192, removeLiquidity_7)
            mstore(224, removeLiquidity_0)
            log1(128, 128, 40601487888975922259554448828720518987931677697835248007167516320394709135098)
            tstore(0, 0)
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
        if callvalue() {
            revert(0, 0)
        }
        tstore(0, 1)
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
            let swap0for1_4 := sload(7)
            let swap0for1_5 := sload(8)
            if iszero(10000) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 18)
                revert(128, 36)
            }
            let swap0for1_6 := mul(swap0for1_0, 9970)
            if iszero(or(iszero(swap0for1_0), eq(div(swap0for1_6, swap0for1_0), 9970))) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            swap0for1_6 := div(swap0for1_6, 10000)
            let swap0for1_7 := add(swap0for1_2, swap0for1_6)
            if lt(swap0for1_7, swap0for1_2) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            if iszero(swap0for1_7) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 18)
                revert(128, 36)
            }
            let swap0for1_8 := mul(swap0for1_3, swap0for1_6)
            if iszero(or(iszero(swap0for1_3), eq(div(swap0for1_8, swap0for1_3), swap0for1_6))) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            swap0for1_8 := div(swap0for1_8, swap0for1_7)
            if lt(swap0for1_0, swap0for1_6) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            let swap0for1_9 := sub(swap0for1_0, swap0for1_6)
            switch eq(swap0for1_4, 0)
            case 0 {
                if iszero(10000) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 18)
                    revert(128, 36)
                }
                let swap0for1_10 := mul(swap0for1_9, swap0for1_5)
                if iszero(or(iszero(swap0for1_9), eq(div(swap0for1_10, swap0for1_9), swap0for1_5))) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                swap0for1_10 := div(swap0for1_10, 10000)
                if iszero(iszero(lt(swap0for1_9, swap0for1_10))) {
                    mstore(128, shl(224, 3444466023))
                    revert(128, 4)
                }
                if iszero(iszero(lt(swap0for1_8, swap0for1_1))) {
                    mstore(128, shl(224, 3139990979))
                    revert(128, 4)
                }
                if iszero(lt(0, swap0for1_8)) {
                    mstore(128, shl(224, 276346163))
                    revert(128, 4)
                }
                if lt(swap0for1_0, swap0for1_10) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                let swap0for1_11 := sub(swap0for1_0, swap0for1_10)
                let swap0for1_12 := add(swap0for1_2, swap0for1_11)
                if lt(swap0for1_12, swap0for1_2) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                sstore(2, swap0for1_12)
                if lt(swap0for1_3, swap0for1_8) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                let swap0for1_13 := sub(swap0for1_3, swap0for1_8)
                sstore(3, swap0for1_13)
                let swap0for1_14 := sload(9)
                let swap0for1_15 := add(swap0for1_14, swap0for1_10)
                if lt(swap0for1_15, swap0for1_14) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                sstore(9, swap0for1_15)
                let swap0for1_16 := caller()
                let swap0for1_17 := address()
                let swap0for1_18 := sload(0)
                let swap0for1_19 := 0
                {
                    mstore(128, shl(224, 599290589))
                    mstore(132, swap0for1_16)
                    mstore(164, swap0for1_17)
                    mstore(196, swap0for1_0)
                    let swap0for1__ok_19 := call(1000000, swap0for1_18, 0, 128, 100, 128, 32)
                    if iszero(swap0for1__ok_19) {
                        revert(0, 0)
                    }
                    if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                        revert(0, 0)
                    }
                    swap0for1_19 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
                }
                if iszero(eq(swap0for1_19, 1)) {
                    mstore(128, shl(224, 2428038168))
                    revert(128, 4)
                }
                let swap0for1_20 := sload(1)
                let swap0for1_21 := 0
                {
                    mstore(128, shl(224, 2835717307))
                    mstore(132, swap0for1_16)
                    mstore(164, swap0for1_8)
                    let swap0for1__ok_21 := call(1000000, swap0for1_20, 0, 128, 68, 128, 32)
                    if iszero(swap0for1__ok_21) {
                        revert(0, 0)
                    }
                    if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                        revert(0, 0)
                    }
                    swap0for1_21 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
                }
                if iszero(eq(swap0for1_21, 1)) {
                    mstore(128, shl(224, 2428038168))
                    revert(128, 4)
                }
                mstore(128, swap0for1_16)
                mstore(160, 1)
                mstore(192, swap0for1_0)
                mstore(224, swap0for1_8)
                log1(128, 128, 86768161654980176899577263720070882195761484507570202454968849668881973053645)
                tstore(0, 0)
                mstore(128, swap0for1_8)
                return(128, 32)
            }
            default {
                if iszero(10000) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 18)
                    revert(128, 36)
                }
                let swap0for1_10 := mul(swap0for1_9, 0)
                if iszero(or(iszero(swap0for1_9), eq(div(swap0for1_10, swap0for1_9), 0))) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                swap0for1_10 := div(swap0for1_10, 10000)
                if iszero(iszero(lt(swap0for1_9, swap0for1_10))) {
                    mstore(128, shl(224, 3444466023))
                    revert(128, 4)
                }
                if iszero(iszero(lt(swap0for1_8, swap0for1_1))) {
                    mstore(128, shl(224, 3139990979))
                    revert(128, 4)
                }
                if iszero(lt(0, swap0for1_8)) {
                    mstore(128, shl(224, 276346163))
                    revert(128, 4)
                }
                if lt(swap0for1_0, swap0for1_10) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                let swap0for1_11 := sub(swap0for1_0, swap0for1_10)
                let swap0for1_12 := add(swap0for1_2, swap0for1_11)
                if lt(swap0for1_12, swap0for1_2) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                sstore(2, swap0for1_12)
                if lt(swap0for1_3, swap0for1_8) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                let swap0for1_13 := sub(swap0for1_3, swap0for1_8)
                sstore(3, swap0for1_13)
                let swap0for1_14 := sload(9)
                let swap0for1_15 := add(swap0for1_14, swap0for1_10)
                if lt(swap0for1_15, swap0for1_14) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                sstore(9, swap0for1_15)
                let swap0for1_16 := caller()
                let swap0for1_17 := address()
                let swap0for1_18 := sload(0)
                let swap0for1_19 := 0
                {
                    mstore(128, shl(224, 599290589))
                    mstore(132, swap0for1_16)
                    mstore(164, swap0for1_17)
                    mstore(196, swap0for1_0)
                    let swap0for1__ok_19 := call(1000000, swap0for1_18, 0, 128, 100, 128, 32)
                    if iszero(swap0for1__ok_19) {
                        revert(0, 0)
                    }
                    if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                        revert(0, 0)
                    }
                    swap0for1_19 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
                }
                if iszero(eq(swap0for1_19, 1)) {
                    mstore(128, shl(224, 2428038168))
                    revert(128, 4)
                }
                let swap0for1_20 := sload(1)
                let swap0for1_21 := 0
                {
                    mstore(128, shl(224, 2835717307))
                    mstore(132, swap0for1_16)
                    mstore(164, swap0for1_8)
                    let swap0for1__ok_21 := call(1000000, swap0for1_20, 0, 128, 68, 128, 32)
                    if iszero(swap0for1__ok_21) {
                        revert(0, 0)
                    }
                    if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                        revert(0, 0)
                    }
                    swap0for1_21 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
                }
                if iszero(eq(swap0for1_21, 1)) {
                    mstore(128, shl(224, 2428038168))
                    revert(128, 4)
                }
                mstore(128, swap0for1_16)
                mstore(160, 1)
                mstore(192, swap0for1_0)
                mstore(224, swap0for1_8)
                log1(128, 128, 86768161654980176899577263720070882195761484507570202454968849668881973053645)
                tstore(0, 0)
                mstore(128, swap0for1_8)
                return(128, 32)
            }
        }
    }
    case 567466531 { // swap1for0(uint256,uint256)
        {
            if lt(calldatasize(), 68) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
        }
        tstore(0, 1)
        {
            let swap1for0_0 := calldataload(4)
            let swap1for0_1 := calldataload(36)
            if iszero(lt(0, swap1for0_0)) {
                mstore(128, shl(224, 4099277827))
                revert(128, 4)
            }
            let swap1for0_2 := sload(3)
            let swap1for0_3 := sload(2)
            if iszero(lt(0, swap1for0_2)) {
                mstore(128, shl(224, 4099277827))
                revert(128, 4)
            }
            if iszero(lt(0, swap1for0_3)) {
                mstore(128, shl(224, 4099277827))
                revert(128, 4)
            }
            let swap1for0_4 := sload(7)
            let swap1for0_5 := sload(8)
            if iszero(10000) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 18)
                revert(128, 36)
            }
            let swap1for0_6 := mul(swap1for0_0, 9970)
            if iszero(or(iszero(swap1for0_0), eq(div(swap1for0_6, swap1for0_0), 9970))) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            swap1for0_6 := div(swap1for0_6, 10000)
            let swap1for0_7 := add(swap1for0_2, swap1for0_6)
            if lt(swap1for0_7, swap1for0_2) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            if iszero(swap1for0_7) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 18)
                revert(128, 36)
            }
            let swap1for0_8 := mul(swap1for0_3, swap1for0_6)
            if iszero(or(iszero(swap1for0_3), eq(div(swap1for0_8, swap1for0_3), swap1for0_6))) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            swap1for0_8 := div(swap1for0_8, swap1for0_7)
            if lt(swap1for0_0, swap1for0_6) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            let swap1for0_9 := sub(swap1for0_0, swap1for0_6)
            switch eq(swap1for0_4, 0)
            case 0 {
                if iszero(10000) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 18)
                    revert(128, 36)
                }
                let swap1for0_10 := mul(swap1for0_9, swap1for0_5)
                if iszero(or(iszero(swap1for0_9), eq(div(swap1for0_10, swap1for0_9), swap1for0_5))) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                swap1for0_10 := div(swap1for0_10, 10000)
                if iszero(iszero(lt(swap1for0_9, swap1for0_10))) {
                    mstore(128, shl(224, 3444466023))
                    revert(128, 4)
                }
                if iszero(iszero(lt(swap1for0_8, swap1for0_1))) {
                    mstore(128, shl(224, 3139990979))
                    revert(128, 4)
                }
                if iszero(lt(0, swap1for0_8)) {
                    mstore(128, shl(224, 276346163))
                    revert(128, 4)
                }
                if lt(swap1for0_0, swap1for0_10) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                let swap1for0_11 := sub(swap1for0_0, swap1for0_10)
                let swap1for0_12 := add(swap1for0_2, swap1for0_11)
                if lt(swap1for0_12, swap1for0_2) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                sstore(3, swap1for0_12)
                if lt(swap1for0_3, swap1for0_8) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                let swap1for0_13 := sub(swap1for0_3, swap1for0_8)
                sstore(2, swap1for0_13)
                let swap1for0_14 := sload(10)
                let swap1for0_15 := add(swap1for0_14, swap1for0_10)
                if lt(swap1for0_15, swap1for0_14) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                sstore(10, swap1for0_15)
                let swap1for0_16 := caller()
                let swap1for0_17 := address()
                let swap1for0_18 := sload(1)
                let swap1for0_19 := 0
                {
                    mstore(128, shl(224, 599290589))
                    mstore(132, swap1for0_16)
                    mstore(164, swap1for0_17)
                    mstore(196, swap1for0_0)
                    let swap1for0__ok_19 := call(1000000, swap1for0_18, 0, 128, 100, 128, 32)
                    if iszero(swap1for0__ok_19) {
                        revert(0, 0)
                    }
                    if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                        revert(0, 0)
                    }
                    swap1for0_19 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
                }
                if iszero(eq(swap1for0_19, 1)) {
                    mstore(128, shl(224, 2428038168))
                    revert(128, 4)
                }
                let swap1for0_20 := sload(0)
                let swap1for0_21 := 0
                {
                    mstore(128, shl(224, 2835717307))
                    mstore(132, swap1for0_16)
                    mstore(164, swap1for0_8)
                    let swap1for0__ok_21 := call(1000000, swap1for0_20, 0, 128, 68, 128, 32)
                    if iszero(swap1for0__ok_21) {
                        revert(0, 0)
                    }
                    if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                        revert(0, 0)
                    }
                    swap1for0_21 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
                }
                if iszero(eq(swap1for0_21, 1)) {
                    mstore(128, shl(224, 2428038168))
                    revert(128, 4)
                }
                mstore(128, swap1for0_16)
                mstore(160, 0)
                mstore(192, swap1for0_0)
                mstore(224, swap1for0_8)
                log1(128, 128, 86768161654980176899577263720070882195761484507570202454968849668881973053645)
                tstore(0, 0)
                mstore(128, swap1for0_8)
                return(128, 32)
            }
            default {
                if iszero(10000) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 18)
                    revert(128, 36)
                }
                let swap1for0_10 := mul(swap1for0_9, 0)
                if iszero(or(iszero(swap1for0_9), eq(div(swap1for0_10, swap1for0_9), 0))) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                swap1for0_10 := div(swap1for0_10, 10000)
                if iszero(iszero(lt(swap1for0_9, swap1for0_10))) {
                    mstore(128, shl(224, 3444466023))
                    revert(128, 4)
                }
                if iszero(iszero(lt(swap1for0_8, swap1for0_1))) {
                    mstore(128, shl(224, 3139990979))
                    revert(128, 4)
                }
                if iszero(lt(0, swap1for0_8)) {
                    mstore(128, shl(224, 276346163))
                    revert(128, 4)
                }
                if lt(swap1for0_0, swap1for0_10) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                let swap1for0_11 := sub(swap1for0_0, swap1for0_10)
                let swap1for0_12 := add(swap1for0_2, swap1for0_11)
                if lt(swap1for0_12, swap1for0_2) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                sstore(3, swap1for0_12)
                if lt(swap1for0_3, swap1for0_8) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                let swap1for0_13 := sub(swap1for0_3, swap1for0_8)
                sstore(2, swap1for0_13)
                let swap1for0_14 := sload(10)
                let swap1for0_15 := add(swap1for0_14, swap1for0_10)
                if lt(swap1for0_15, swap1for0_14) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                sstore(10, swap1for0_15)
                let swap1for0_16 := caller()
                let swap1for0_17 := address()
                let swap1for0_18 := sload(1)
                let swap1for0_19 := 0
                {
                    mstore(128, shl(224, 599290589))
                    mstore(132, swap1for0_16)
                    mstore(164, swap1for0_17)
                    mstore(196, swap1for0_0)
                    let swap1for0__ok_19 := call(1000000, swap1for0_18, 0, 128, 100, 128, 32)
                    if iszero(swap1for0__ok_19) {
                        revert(0, 0)
                    }
                    if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                        revert(0, 0)
                    }
                    swap1for0_19 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
                }
                if iszero(eq(swap1for0_19, 1)) {
                    mstore(128, shl(224, 2428038168))
                    revert(128, 4)
                }
                let swap1for0_20 := sload(0)
                let swap1for0_21 := 0
                {
                    mstore(128, shl(224, 2835717307))
                    mstore(132, swap1for0_16)
                    mstore(164, swap1for0_8)
                    let swap1for0__ok_21 := call(1000000, swap1for0_20, 0, 128, 68, 128, 32)
                    if iszero(swap1for0__ok_21) {
                        revert(0, 0)
                    }
                    if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                        revert(0, 0)
                    }
                    swap1for0_21 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
                }
                if iszero(eq(swap1for0_21, 1)) {
                    mstore(128, shl(224, 2428038168))
                    revert(128, 4)
                }
                mstore(128, swap1for0_16)
                mstore(160, 0)
                mstore(192, swap1for0_0)
                mstore(224, swap1for0_8)
                log1(128, 128, 86768161654980176899577263720070882195761484507570202454968849668881973053645)
                tstore(0, 0)
                mstore(128, swap1for0_8)
                return(128, 32)
            }
        }
    }
    case 3466333111 { // setProtocolShare(uint256)
        {
            if lt(calldatasize(), 36) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
        }
        {
            let setProtocolShare_0 := calldataload(4)
            let setProtocolShare_1 := caller()
            let setProtocolShare_2 := sload(6)
            if iszero(eq(setProtocolShare_1, setProtocolShare_2)) {
                mstore(128, shl(224, 818771057))
                revert(128, 4)
            }
            if iszero(iszero(lt(10000, setProtocolShare_0))) {
                mstore(128, shl(224, 3444466023))
                revert(128, 4)
            }
            sstore(8, setProtocolShare_0)
            mstore(128, setProtocolShare_0)
            log1(128, 32, 78079718419834948551627908205665023158928999810385303473344028204908084497237)
            stop()
        }
    }
    case 4100522477 { // setFeeTo(address)
        {
            if lt(calldatasize(), 36) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
        }
        {
            let setFeeTo_0 := calldataload(4)
            let setFeeTo_1 := caller()
            let setFeeTo_2 := sload(6)
            if iszero(eq(setFeeTo_1, setFeeTo_2)) {
                mstore(128, shl(224, 818771057))
                revert(128, 4)
            }
            sstore(7, setFeeTo_0)
            mstore(128, setFeeTo_0)
            log1(128, 32, 104813359228667965264018616497249306493976232541265610150824559774497769035132)
            stop()
        }
    }
    case 2712624026 { // collectProtocolFees()
        {
            if lt(calldatasize(), 4) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
        }
        tstore(0, 1)
        {
            let collectProtocolFees_0 := caller()
            let collectProtocolFees_1 := sload(7)
            if iszero(iszero(eq(collectProtocolFees_1, 0))) {
                mstore(128, shl(224, 1869924957))
                revert(128, 4)
            }
            if iszero(eq(collectProtocolFees_0, collectProtocolFees_1)) {
                mstore(128, shl(224, 818771057))
                revert(128, 4)
            }
            let collectProtocolFees_2 := sload(9)
            let collectProtocolFees_3 := sload(10)
            sstore(9, 0)
            sstore(10, 0)
            let collectProtocolFees_4 := sload(0)
            let collectProtocolFees_5 := sload(1)
            let collectProtocolFees_6 := 0
            {
                mstore(128, shl(224, 2835717307))
                mstore(132, collectProtocolFees_0)
                mstore(164, collectProtocolFees_2)
                let collectProtocolFees__ok_6 := call(1000000, collectProtocolFees_4, 0, 128, 68, 128, 32)
                if iszero(collectProtocolFees__ok_6) {
                    revert(0, 0)
                }
                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                    revert(0, 0)
                }
                collectProtocolFees_6 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
            }
            if iszero(eq(collectProtocolFees_6, 1)) {
                mstore(128, shl(224, 2428038168))
                revert(128, 4)
            }
            let collectProtocolFees_7 := 0
            {
                mstore(128, shl(224, 2835717307))
                mstore(132, collectProtocolFees_0)
                mstore(164, collectProtocolFees_3)
                let collectProtocolFees__ok_7 := call(1000000, collectProtocolFees_5, 0, 128, 68, 128, 32)
                if iszero(collectProtocolFees__ok_7) {
                    revert(0, 0)
                }
                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), lt(returndatasize(), 64)))) {
                    revert(0, 0)
                }
                collectProtocolFees_7 := or(iszero(returndatasize()), iszero(iszero(mload(128))))
            }
            if iszero(eq(collectProtocolFees_7, 1)) {
                mstore(128, shl(224, 2428038168))
                revert(128, 4)
            }
            mstore(128, collectProtocolFees_0)
            mstore(160, collectProtocolFees_2)
            mstore(192, collectProtocolFees_3)
            log1(128, 96, 95121392122185204562677465797196329875905566723564389279626642440448997759761)
            tstore(0, 0)
            mstore(128, collectProtocolFees_2)
            mstore(160, collectProtocolFees_3)
            return(128, 64)
        }
    }
    case 151187884 { // getReserves()
        {
            if lt(calldatasize(), 4) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
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
        if callvalue() {
            revert(0, 0)
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
    case 450408507 { // protocolFees()
        {
            if lt(calldatasize(), 4) {
                revert(0, 0)
            }
        }
        if callvalue() {
            revert(0, 0)
        }
        {
            let protocolFees_0 := sload(9)
            let protocolFees_1 := sload(10)
            mstore(128, protocolFees_0)
            mstore(160, protocolFees_1)
            return(128, 64)
        }
    }
    default {
        revert(0, 0)
    }
}
