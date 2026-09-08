// selector → function  (hex and decimal; `switch` cases print decimal)
//   0xd09de08a  (3500007562)  increment()
//   0x03df179c  (64952220)  incrementBy(uint256)
//   0x2baeceb7  (732876471)  decrement()
//   0x6d4ce63c  (1833756220)  get()

{
    if memoryguard(256) {
    }
    {
        if lt(calldatasize(), 4) {
            revert(0, 0)
        }
    }
    switch shr(224, calldataload(0))
    case 3500007562 { // increment()
        {
            if lt(calldatasize(), 4) {
                revert(0, 0)
            }
        }
        {
            let increment_0 := sload(0)
            let increment_1 := add(increment_0, 1)
            if lt(increment_1, increment_0) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            sstore(0, increment_1)
            mstore(128, 1)
            log1(128, 32, 14856802433279870282832221894547230581069000514227772933392656809679562378628)
            stop()
        }
    }
    case 64952220 { // incrementBy(uint256)
        {
            if lt(calldatasize(), 36) {
                revert(0, 0)
            }
        }
        {
            let incrementBy_0 := calldataload(4)
            if iszero(iszero(eq(incrementBy_0, 0))) {
                mstore(128, shl(224, 4099277827))
                revert(128, 4)
            }
            let incrementBy_1 := sload(0)
            let incrementBy_2 := add(incrementBy_1, incrementBy_0)
            if lt(incrementBy_2, incrementBy_1) {
                mstore(128, shl(224, 1313373041))
                mstore(132, 17)
                revert(128, 36)
            }
            sstore(0, incrementBy_2)
            mstore(128, incrementBy_0)
            log1(128, 32, 14856802433279870282832221894547230581069000514227772933392656809679562378628)
            stop()
        }
    }
    case 732876471 { // decrement()
        {
            if lt(calldatasize(), 4) {
                revert(0, 0)
            }
        }
        {
            let decrement_0 := sload(0)
            switch eq(decrement_0, 0)
            case 0 {
                if lt(decrement_0, 1) {
                    mstore(128, shl(224, 1313373041))
                    mstore(132, 17)
                    revert(128, 36)
                }
                let decrement_1 := sub(decrement_0, 1)
                sstore(0, decrement_1)
                stop()
            }
            default {
                let decrement_1 := 0
                sstore(0, decrement_1)
                stop()
            }
        }
    }
    case 1833756220 { // get()
        {
            if lt(calldatasize(), 4) {
                revert(0, 0)
            }
        }
        {
            let get_0 := sload(0)
            mstore(128, get_0)
            return(128, 32)
        }
    }
    default {
        revert(0, 0)
    }
}
