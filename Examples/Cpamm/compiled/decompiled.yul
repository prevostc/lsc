/// @title            Decompiled Contract
/// @author           Jonathan Becker <jonathan@jbecker.dev>
/// @custom:version   heimdall-rs v0.9.2
///
/// @notice           This contract was decompiled using the heimdall-rs decompiler.
///                     It was generated directly by tracing the EVM opcodes from this contract.
///                     As a result, it may not compile or even be valid yul code.
///                     Despite this, it should be obvious what each function does. Overall
///                     logic should have been preserved throughout decompiling.
///
/// @custom:github    You can find the open-source decompiler here:
///                       https://heimdall.rs

object "DecompiledContract" {
    object "runtime" {
        code {
            
            function selector() -> s {
                s := div(calldataload(0), 0x100000000000000000000000000000000000000000000000000000000)
            }
            
            function castToAddress(x) -> a {
                a := and(x, 0xffffffffffffffffffffffffffffffffffffffff)
            }
            
            switch selector()
            
            /*
            * @custom:signature    Unresolved_2b1087f0(uint256 arg0, uint256 arg1) public payable returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            * @param                arg1 ["uint256", "bytes32", "int256"]
            */
            case 0x2b1087f0 {
                if iszero(lt(calldatasize(), 0x44)) {
                    mstore(0x0100, calldataload(0x04))
                    if lt(0, mload(0x0100)) {
                        if lt(0, sload(0)) {
                            if lt(0, sload(0x01)) {
                                if 0x2710 {
                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                    mstore(0x84, 0x12)
                                    if or(iszero(mload(0x0100)), eq(div(mul(mload(0x0100), 0x26f2), mload(0x0100)), 0x26f2)) {
                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                        mstore(0x84, 0x11)
                                        if iszero(lt(add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0))) {
                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                            mstore(0x84, 0x11)
                                            if add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710)) {
                                                if or(iszero(div(mul(mload(0x0100), 0x26f2), 0x2710)), eq(div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x01))) {
                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                    mstore(0x84, 0x11)
                                                    if iszero(lt(div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710))), calldataload(0x24))) { revert(0x80, 0x04); } else {
                                                        mstore(0x80, 0xbb2875c300000000000000000000000000000000000000000000000000000000)
                                                        if lt(0, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710)))) {
                                                            if eq(0, eq(sload(0x09), 0)) {
                                                                if 0x2710 {
                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                    mstore(0x84, 0x12)
                                                                    if or(iszero(mload(0x0100)), eq(div(mul(mload(0x0100), 0x26f2), mload(0x0100)), 0x26f2)) {
                                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                        mstore(0x84, 0x11)
                                                                        if iszero(lt(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710))) {
                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                            mstore(0x84, 0x11)
                                                                            if 0x2710 {
                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                mstore(0x84, 0x12)
                                                                                if or(iszero(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710))), eq(div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x0a)), sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710))), sload(0x0a))) {
                                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                    mstore(0x84, 0x11)
                                                                                    if iszero(lt(mload(0x0100), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x0a)), 0x2710))) {
                                                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                        mstore(0x84, 0x11)
                                                                                        if iszero(lt(add(sload(0), sub(mload(0x0100), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x0a)), 0x2710))), sload(0))) {
                                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                            mstore(0x84, 0x11)
                                                                                            sstore(0, add(sload(0), sub(mload(0x0100), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x0a)), 0x2710))))
                                                                                            if iszero(lt(sload(0x01), div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710))))) {
                                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                mstore(0x84, 0x11)
                                                                                                sstore(0x01, sub(sload(0x01), div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710)))))
                                                                                                if iszero(lt(add(sload(0x0b), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x0a)), 0x2710)), sload(0x0b))) {
                                                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                    mstore(0x84, 0x11)
                                                                                                    sstore(0x0b, add(sload(0x0b), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x0a)), 0x2710)))
                                                                                                    mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                                                    mstore(0x84, caller())
                                                                                                    mstore(0xa4, address())
                                                                                                    mstore(0xc4, mload(0x0100))
                                                                                                    call(0x0f4240, sload(0x04), 0, 0x80, 0x64, 0x80, 0x20)
                                                                                                    if call(0x0f4240, sload(0x04), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                        if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                            if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                                                                                mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                                                                                                                mstore(0x84, caller())
                                                                                                                mstore(0xa4, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                call(0x0f4240, sload(0x05), 0, 0x80, 0x44, 0x80, 0x20)
                                                                                                                if call(0x0f4240, sload(0x05), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                    if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                                        if iszero(eq(0x01, 0)) { revert(0, 0); } else {
                                                                                                                            mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                            mstore(0x80, caller())
                                                                                                                            mstore(0xa0, mload(0x0100))
                                                                                                                            mstore(0xc0, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                            log1(0x80, 0x60, 0x268d208c45ec3d7213f545c4402b1bc7f11b332757a4e0d84ff4d37b90db1fca)
                                                                                                                            mstore(0x80, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                            return(0x80, 0x20)
                                                                                                                            if iszero(lt(add(sload(0), mload(0x0100)), sload(0))) {
                                                                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                mstore(0x84, 0x11)
                                                                                                                                sstore(0, add(sload(0), mload(0x0100)))
                                                                                                                                if iszero(lt(sload(0x01), div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710))))) {
                                                                                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                    mstore(0x84, 0x11)
                                                                                                                                    sstore(0x01, sub(sload(0x01), div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710)))))
                                                                                                                                    mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                                                                                    mstore(0x84, caller())
                                                                                                                                    mstore(0xa4, address())
                                                                                                                                    mstore(0xc4, mload(0x0100))
                                                                                                                                    call(0x0f4240, sload(0x04), 0, 0x80, 0x64, 0x80, 0x20)
                                                                                                                                    if call(0x0f4240, sload(0x04), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                                        if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                                                            if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                                                                                                                mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                                                mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                                                                                                                                                mstore(0x84, caller())
                                                                                                                                                mstore(0xa4, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                                                call(0x0f4240, sload(0x05), 0, 0x80, 0x44, 0x80, 0x20)
                                                                                                                                                if call(0x0f4240, sload(0x05), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                                                    if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                                                                        if iszero(eq(0x01, 0)) { revert(0, 0); } else {
                                                                                                                                                            mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x80, caller())
                                                                                                                                                            mstore(0xa0, mload(0x0100))
                                                                                                                                                            mstore(0xc0, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                                                            log1(0x80, 0x60, 0x268d208c45ec3d7213f545c4402b1bc7f11b332757a4e0d84ff4d37b90db1fca)
                                                                                                                                                            mstore(0x80, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0x01)), add(sload(0), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                                                            return(0x80, 0x20)
                                                                                                                                                            mstore(0x80, 0x1078b53300000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x84, 0x12)
                                                                                                                                                            mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                                                                                                        }
                                                                                                                                                    }
                                                                                                                                                }
                                                                                                                                            }
                                                                                                                                        }
                                                                                                                                    }
                                                                                                                                }
                                                                                                                            }
                                                                                                                        }
                                                                                                                    }
                                                                                                                }
                                                                                                            }
                                                                                                        }
                                                                                                    }
                                                                                                }
                                                                                            }
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_a1af5b9a() public payable returns (bytes memory)
            */
            case 0xa1af5b9a {
                if iszero(lt(calldatasize(), 0x04)) { revert(0, 0); } else {
                    if iszero(eq(sload(0x09), 0)) {
                        if eq(caller(), sload(0x09)) { revert(0x80, 0x04); } else {
                            mstore(0x80, 0x30cd747100000000000000000000000000000000000000000000000000000000)
                            sstore(0x0b, 0)
                            sstore(0x0c, 0)
                            mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                            mstore(0x84, caller())
                            mstore(0xa4, sload(0x0b))
                            call(0x0f4240, sload(0x04), 0, 0x80, 0x44, 0x80, 0x20)
                            if call(0x0f4240, sload(0x04), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                    if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                        mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                        mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                                        mstore(0x84, caller())
                                        mstore(0xa4, sload(0x0c))
                                        call(0x0f4240, sload(0x05), 0, 0x80, 0x44, 0x80, 0x20)
                                        if call(0x0f4240, sload(0x05), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                            if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                    mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                    mstore(0x80, caller())
                                                    mstore(0xa0, sload(0x0b))
                                                    mstore(0xc0, sload(0x0c))
                                                    log1(0x80, 0x60, 0xd24ccccf373129a9579bb9f5edc41c09218d54ae950e90b4d5ca2927b7c29b11)
                                                    mstore(0x80, sload(0x0b))
                                                    mstore(0xa0, sload(0x0c))
                                                    return(0x80, 0x40)
                                                    mstore(0x80, 0x6f74ca5d00000000000000000000000000000000000000000000000000000000)
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_1ad8b03b() public view returns (bytes memory)
            */
            case 0x1ad8b03b {
                if iszero(lt(calldatasize(), 0x04)) { revert(0, 0); } else {
                    mstore(0x80, sload(0x0b))
                    mstore(0xa0, sload(0x0c))
                    return(0x80, 0x40)
                }
            }
            
            /*
            * @custom:signature    Unresolved_9cd441da(uint256 arg0, uint256 arg1) public payable returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            * @param                arg1 ["uint256", "bytes32", "int256"]
            */
            case 0x9cd441da {
                if iszero(lt(calldatasize(), 0x44)) {
                    mstore(0x0100, calldataload(0x04))
                    mstore(0x0120, calldataload(0x24))
                    if lt(0, mload(0x0100)) {
                        if lt(0, mload(0x0120)) {
                            if eq(0, eq(sload(0x02), 0)) {
                                if lt(0, sload(0)) {
                                    if lt(0, sload(0x01)) {
                                        if sload(0) {
                                            if or(iszero(mload(0x0100)), eq(div(mul(mload(0x0100), sload(0x02)), mload(0x0100)), sload(0x02))) {
                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                mstore(0x84, 0x11)
                                                if sload(0x01) {
                                                    if or(iszero(mload(0x0120)), eq(div(mul(mload(0x0120), sload(0x02)), mload(0x0120)), sload(0x02))) {
                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                        mstore(0x84, 0x11)
                                                        if eq(0, iszero(lt(div(mul(mload(0x0120), sload(0x02)), sload(0x01)), div(mul(mload(0x0100), sload(0x02)), sload(0))))) {
                                                            if lt(0, div(mul(mload(0x0120), sload(0x02)), sload(0x01))) {
                                                                if iszero(lt(add(sload(0), mload(0x0100)), sload(0))) {
                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                    mstore(0x84, 0x11)
                                                                    sstore(0, add(sload(0), mload(0x0100)))
                                                                    if iszero(lt(add(sload(0x01), mload(0x0120)), sload(0x01))) {
                                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                        mstore(0x84, 0x11)
                                                                        sstore(0x01, add(sload(0x01), mload(0x0120)))
                                                                        if iszero(lt(add(div(mul(mload(0x0120), sload(0x02)), sload(0x01)), sload(0x02)), div(mul(mload(0x0120), sload(0x02)), sload(0x01)))) {
                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                            mstore(0x84, 0x11)
                                                                            sstore(0x02, add(div(mul(mload(0x0120), sload(0x02)), sload(0x01)), sload(0x02)))
                                                                            mstore(0, caller())
                                                                            mstore(0x20, 0x03)
                                                                            if iszero(lt(add(div(mul(mload(0x0120), sload(0x02)), sload(0x01)), sload(sha3(0, 0x40))), div(mul(mload(0x0120), sload(0x02)), sload(0x01)))) {
                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                mstore(0x84, 0x11)
                                                                                mstore(0, caller())
                                                                                mstore(0x20, 0x03)
                                                                                sstore(sha3(0, 0x40), add(div(mul(mload(0x0120), sload(0x02)), sload(0x01)), sload(sha3(0, 0x40))))
                                                                                mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                                mstore(0x84, caller())
                                                                                mstore(0xa4, address())
                                                                                mstore(0xc4, mload(0x0100))
                                                                                call(0x0f4240, sload(0x04), 0, 0x80, 0x64, 0x80, 0x20)
                                                                                if call(0x0f4240, sload(0x04), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                                    if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                        if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                                                            mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                            mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                                            mstore(0x84, caller())
                                                                                            mstore(0xa4, address())
                                                                                            mstore(0xc4, mload(0x0120))
                                                                                            call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20)
                                                                                            if call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                    if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                                                                        mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                        mstore(0x80, caller())
                                                                                                        mstore(0xa0, mload(0x0100))
                                                                                                        mstore(0xc0, mload(0x0120))
                                                                                                        mstore(0xe0, div(mul(mload(0x0120), sload(0x02)), sload(0x01)))
                                                                                                        log1(0x80, 0x80, 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce)
                                                                                                        mstore(0x80, div(mul(mload(0x0120), sload(0x02)), sload(0x01)))
                                                                                                        return(0x80, 0x20)
                                                                                                        mstore(0x80, 0x9811e0c700000000000000000000000000000000000000000000000000000000)
                                                                                                        if lt(0, div(mul(mload(0x0100), sload(0x02)), sload(0))) {
                                                                                                            if iszero(lt(add(sload(0), mload(0x0100)), sload(0))) {
                                                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                mstore(0x84, 0x11)
                                                                                                                sstore(0, add(sload(0), mload(0x0100)))
                                                                                                                if iszero(lt(add(sload(0x01), mload(0x0120)), sload(0x01))) {
                                                                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                    mstore(0x84, 0x11)
                                                                                                                    sstore(0x01, add(sload(0x01), mload(0x0120)))
                                                                                                                    if iszero(lt(add(div(mul(mload(0x0100), sload(0x02)), sload(0)), sload(0x02)), div(mul(mload(0x0100), sload(0x02)), sload(0)))) {
                                                                                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                        mstore(0x84, 0x11)
                                                                                                                        sstore(0x02, add(div(mul(mload(0x0100), sload(0x02)), sload(0)), sload(0x02)))
                                                                                                                        mstore(0, caller())
                                                                                                                        mstore(0x20, 0x03)
                                                                                                                        if iszero(lt(add(div(mul(mload(0x0100), sload(0x02)), sload(0)), sload(sha3(0, 0x40))), div(mul(mload(0x0100), sload(0x02)), sload(0)))) {
                                                                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                            mstore(0x84, 0x11)
                                                                                                                            mstore(0, caller())
                                                                                                                            mstore(0x20, 0x03)
                                                                                                                            sstore(sha3(0, 0x40), add(div(mul(mload(0x0100), sload(0x02)), sload(0)), sload(sha3(0, 0x40))))
                                                                                                                            mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                                                                            mstore(0x84, caller())
                                                                                                                            mstore(0xa4, address())
                                                                                                                            mstore(0xc4, mload(0x0100))
                                                                                                                            call(0x0f4240, sload(0x04), 0, 0x80, 0x64, 0x80, 0x20)
                                                                                                                            if call(0x0f4240, sload(0x04), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                                if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                                                    if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                                                                                                        mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                                        mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                                                                                        mstore(0x84, caller())
                                                                                                                                        mstore(0xa4, address())
                                                                                                                                        mstore(0xc4, mload(0x0120))
                                                                                                                                        call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20)
                                                                                                                                        if call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                                            if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                                                                if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                                                                                                                    mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                                                    mstore(0x80, caller())
                                                                                                                                                    mstore(0xa0, mload(0x0100))
                                                                                                                                                    mstore(0xc0, mload(0x0120))
                                                                                                                                                    mstore(0xe0, div(mul(mload(0x0100), sload(0x02)), sload(0)))
                                                                                                                                                    log1(0x80, 0x80, 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce)
                                                                                                                                                    mstore(0x80, div(mul(mload(0x0100), sload(0x02)), sload(0)))
                                                                                                                                                    return(0x80, 0x20)
                                                                                                                                                    mstore(0x80, 0x9811e0c700000000000000000000000000000000000000000000000000000000)
                                                                                                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                                    mstore(0x84, 0x12)
                                                                                                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                                    mstore(0x84, 0x12)
                                                                                                                                                    mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                                                                                                    mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                                                                                                    if lt(0, mload(0x0100)) {
                                                                                                                                                        if iszero(lt(add(sload(0), mload(0x0100)), sload(0))) {
                                                                                                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x84, 0x11)
                                                                                                                                                            sstore(0, add(sload(0), mload(0x0100)))
                                                                                                                                                            if iszero(lt(add(sload(0x01), mload(0x0120)), sload(0x01))) {
                                                                                                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                mstore(0x84, 0x11)
                                                                                                                                                                sstore(0x01, add(sload(0x01), mload(0x0120)))
                                                                                                                                                                if iszero(lt(add(mload(0x0100), sload(0x02)), mload(0x0100))) {
                                                                                                                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                    mstore(0x84, 0x11)
                                                                                                                                                                    sstore(0x02, add(mload(0x0100), sload(0x02)))
                                                                                                                                                                    mstore(0, caller())
                                                                                                                                                                    mstore(0x20, 0x03)
                                                                                                                                                                    if iszero(lt(add(mload(0x0100), sload(sha3(0, 0x40))), mload(0x0100))) {
                                                                                                                                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                        mstore(0x84, 0x11)
                                                                                                                                                                        mstore(0, caller())
                                                                                                                                                                        mstore(0x20, 0x03)
                                                                                                                                                                        sstore(sha3(0, 0x40), add(mload(0x0100), sload(sha3(0, 0x40))))
                                                                                                                                                                        mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                        mstore(0x84, caller())
                                                                                                                                                                        mstore(0xa4, address())
                                                                                                                                                                        mstore(0xc4, mload(0x0100))
                                                                                                                                                                        call(0x0f4240, sload(0x04), 0, 0x80, 0x64, 0x80, 0x20)
                                                                                                                                                                        if call(0x0f4240, sload(0x04), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                                                                            if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                                                                                                if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                                                                                                                                                    mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                                    mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                                    mstore(0x84, caller())
                                                                                                                                                                                    mstore(0xa4, address())
                                                                                                                                                                                    mstore(0xc4, mload(0x0120))
                                                                                                                                                                                    call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20)
                                                                                                                                                                                    if call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                                                                                        if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                                                                                                            if iszero(eq(0x01, 0)) { revert(0, 0); } else {
                                                                                                                                                                                                mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                                                mstore(0x80, caller())
                                                                                                                                                                                                mstore(0xa0, mload(0x0100))
                                                                                                                                                                                                mstore(0xc0, mload(0x0120))
                                                                                                                                                                                                mstore(0xe0, mload(0x0100))
                                                                                                                                                                                                log1(0x80, 0x80, 0xbeb3885786d637a474cbc287c0a44587231633a077f0bd30354d5a4b18996fce)
                                                                                                                                                                                                mstore(0x80, mload(0x0100))
                                                                                                                                                                                                return(0x80, 0x20)
                                                                                                                                                                                                mstore(0x80, 0x9811e0c700000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                                                mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                                                mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                                            }
                                                                                                                                                                                        }
                                                                                                                                                                                    }
                                                                                                                                                                                }
                                                                                                                                                                            }
                                                                                                                                                                        }
                                                                                                                                                                    }
                                                                                                                                                                }
                                                                                                                                                            }
                                                                                                                                                        }
                                                                                                                                                    }
                                                                                                                                                }
                                                                                                                                            }
                                                                                                                                        }
                                                                                                                                    }
                                                                                                                                }
                                                                                                                            }
                                                                                                                        }
                                                                                                                    }
                                                                                                                }
                                                                                                            }
                                                                                                        }
                                                                                                    }
                                                                                                }
                                                                                            }
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_9c8f9f23(uint256 arg0) public payable returns (bytes memory)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            */
            case 0x9c8f9f23 {
                if iszero(lt(calldatasize(), 0x24)) {
                    if lt(0, calldataload(0x04)) {
                        mstore(0, caller())
                        mstore(0x20, 0x03)
                        if iszero(lt(sload(sha3(0, 0x40)), calldataload(0x04))) { revert(0x80, 0x04); } else {
                            mstore(0x80, 0x3999656700000000000000000000000000000000000000000000000000000000)
                            if lt(0, sload(0x02)) {
                                if sload(0x02) {
                                    if or(iszero(calldataload(0x04)), eq(div(mul(calldataload(0x04), sload(0)), calldataload(0x04)), sload(0))) {
                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                        mstore(0x84, 0x11)
                                        if sload(0x02) {
                                            if or(iszero(calldataload(0x04)), eq(div(mul(calldataload(0x04), sload(0x01)), calldataload(0x04)), sload(0x01))) {
                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                mstore(0x84, 0x11)
                                                if lt(0, div(mul(calldataload(0x04), sload(0)), sload(0x02))) {
                                                    if lt(0, div(mul(calldataload(0x04), sload(0x01)), sload(0x02))) {
                                                        if iszero(lt(sload(sha3(0, 0x40)), calldataload(0x04))) {
                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                            mstore(0x84, 0x11)
                                                            mstore(0, caller())
                                                            mstore(0x20, 0x03)
                                                            sstore(sha3(0, 0x40), sub(sload(sha3(0, 0x40)), calldataload(0x04)))
                                                            if iszero(lt(sload(0x02), calldataload(0x04))) {
                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                mstore(0x84, 0x11)
                                                                sstore(0x02, sub(sload(0x02), calldataload(0x04)))
                                                                if iszero(lt(sload(0), div(mul(calldataload(0x04), sload(0)), sload(0x02)))) {
                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                    mstore(0x84, 0x11)
                                                                    sstore(0, sub(sload(0), div(mul(calldataload(0x04), sload(0)), sload(0x02))))
                                                                    if iszero(lt(sload(0x01), div(mul(calldataload(0x04), sload(0x01)), sload(0x02)))) {
                                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                        mstore(0x84, 0x11)
                                                                        sstore(0x01, sub(sload(0x01), div(mul(calldataload(0x04), sload(0x01)), sload(0x02))))
                                                                        mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                                                                        mstore(0x84, caller())
                                                                        mstore(0xa4, div(mul(calldataload(0x04), sload(0)), sload(0x02)))
                                                                        call(0x0f4240, sload(0x04), 0, 0x80, 0x44, 0x80, 0x20)
                                                                        if call(0x0f4240, sload(0x04), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                                                            if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                                                    mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                    mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                                                                                    mstore(0x84, caller())
                                                                                    mstore(0xa4, div(mul(calldataload(0x04), sload(0x01)), sload(0x02)))
                                                                                    call(0x0f4240, sload(0x05), 0, 0x80, 0x44, 0x80, 0x20)
                                                                                    if call(0x0f4240, sload(0x05), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                                                                        if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                            if iszero(eq(0x01, 0)) { revert(0, 0); } else {
                                                                                                mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                mstore(0x80, caller())
                                                                                                mstore(0xa0, div(mul(calldataload(0x04), sload(0)), sload(0x02)))
                                                                                                mstore(0xc0, div(mul(calldataload(0x04), sload(0x01)), sload(0x02)))
                                                                                                mstore(0xe0, calldataload(0x04))
                                                                                                log1(0x80, 0x80, 0x59c3a0b60c6ab7deb62e1440c9e72441db6db7dfe514dba8cb18e60c0d896efa)
                                                                                                mstore(0x80, div(mul(calldataload(0x04), sload(0)), sload(0x02)))
                                                                                                mstore(0xa0, div(mul(calldataload(0x04), sload(0x01)), sload(0x02)))
                                                                                                return(0x80, 0x40)
                                                                                                mstore(0x80, 0x1078b53300000000000000000000000000000000000000000000000000000000)
                                                                                                mstore(0x80, 0x1078b53300000000000000000000000000000000000000000000000000000000)
                                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                mstore(0x84, 0x12)
                                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                mstore(0x84, 0x12)
                                                                                                mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                                                mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                                            }
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_f46901ed(uint256 arg0) public payable
            * @param                arg0 ["uint256", "bytes32", "int256"]
            */
            case 0xf46901ed {
                if iszero(lt(calldatasize(), 0x24)) {
                    if eq(caller(), sload(0x08)) { revert(0, 0); } else {
                        mstore(0x80, 0x30cd747100000000000000000000000000000000000000000000000000000000)
                        sstore(0x09, calldataload(0x04))
                        mstore(0x80, calldataload(0x04))
                        log1(0x80, 0x20, 0xe7ba424f407983edfb652af33e51f926d1d41a22bb4850c65eb21c02e378957c)
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_21d2da23(uint256 arg0, uint256 arg1) public payable returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            * @param                arg1 ["uint256", "bytes32", "int256"]
            */
            case 0x21d2da23 {
                if iszero(lt(calldatasize(), 0x44)) {
                    mstore(0x0100, calldataload(0x04))
                    if lt(0, mload(0x0100)) {
                        if lt(0, sload(0)) {
                            if lt(0, sload(0x01)) {
                                if 0x2710 {
                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                    mstore(0x84, 0x12)
                                    if or(iszero(mload(0x0100)), eq(div(mul(mload(0x0100), 0x26f2), mload(0x0100)), 0x26f2)) {
                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                        mstore(0x84, 0x11)
                                        if iszero(lt(add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x01))) {
                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                            mstore(0x84, 0x11)
                                            if add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710)) {
                                                if or(iszero(div(mul(mload(0x0100), 0x26f2), 0x2710)), eq(div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0))) {
                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                    mstore(0x84, 0x11)
                                                    if iszero(lt(div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710))), calldataload(0x24))) { revert(0x80, 0x04); } else {
                                                        mstore(0x80, 0xbb2875c300000000000000000000000000000000000000000000000000000000)
                                                        if lt(0, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710)))) {
                                                            if eq(0, eq(sload(0x09), 0)) {
                                                                if 0x2710 {
                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                    mstore(0x84, 0x12)
                                                                    if or(iszero(mload(0x0100)), eq(div(mul(mload(0x0100), 0x26f2), mload(0x0100)), 0x26f2)) {
                                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                        mstore(0x84, 0x11)
                                                                        if iszero(lt(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710))) {
                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                            mstore(0x84, 0x11)
                                                                            if 0x2710 {
                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                mstore(0x84, 0x12)
                                                                                if or(iszero(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710))), eq(div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x0a)), sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710))), sload(0x0a))) {
                                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                    mstore(0x84, 0x11)
                                                                                    if iszero(lt(mload(0x0100), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x0a)), 0x2710))) {
                                                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                        mstore(0x84, 0x11)
                                                                                        if iszero(lt(add(sload(0x01), sub(mload(0x0100), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x0a)), 0x2710))), sload(0x01))) {
                                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                            mstore(0x84, 0x11)
                                                                                            sstore(0x01, add(sload(0x01), sub(mload(0x0100), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x0a)), 0x2710))))
                                                                                            if iszero(lt(sload(0), div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710))))) {
                                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                mstore(0x84, 0x11)
                                                                                                sstore(0, sub(sload(0), div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710)))))
                                                                                                if iszero(lt(add(sload(0x0c), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x0a)), 0x2710)), sload(0x0c))) {
                                                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                    mstore(0x84, 0x11)
                                                                                                    sstore(0x0c, add(sload(0x0c), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x0a)), 0x2710)))
                                                                                                    mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                                                    mstore(0x84, caller())
                                                                                                    mstore(0xa4, address())
                                                                                                    mstore(0xc4, mload(0x0100))
                                                                                                    call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20)
                                                                                                    if call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                        if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                            if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                                                                                mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                                                                                                                mstore(0x84, caller())
                                                                                                                mstore(0xa4, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                call(0x0f4240, sload(0x04), 0, 0x80, 0x44, 0x80, 0x20)
                                                                                                                if call(0x0f4240, sload(0x04), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                    if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                                        if iszero(eq(0x01, 0)) { revert(0, 0); } else {
                                                                                                                            mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                            mstore(0x80, caller())
                                                                                                                            mstore(0xa0, mload(0x0100))
                                                                                                                            mstore(0xc0, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                            log1(0x80, 0x60, 0xec43a82fae8c251f7aae4f79accf59c765bd798d597ccfd95beef20bf096cc9e)
                                                                                                                            mstore(0x80, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                            return(0x80, 0x20)
                                                                                                                            if iszero(lt(add(sload(0x01), mload(0x0100)), sload(0x01))) {
                                                                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                mstore(0x84, 0x11)
                                                                                                                                sstore(0x01, add(sload(0x01), mload(0x0100)))
                                                                                                                                if iszero(lt(sload(0), div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710))))) {
                                                                                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                    mstore(0x84, 0x11)
                                                                                                                                    sstore(0, sub(sload(0), div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710)))))
                                                                                                                                    mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                                                                                    mstore(0x84, caller())
                                                                                                                                    mstore(0xa4, address())
                                                                                                                                    mstore(0xc4, mload(0x0100))
                                                                                                                                    call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20)
                                                                                                                                    if call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                                        if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                                                            if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                                                                                                                mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                                                mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                                                                                                                                                mstore(0x84, caller())
                                                                                                                                                mstore(0xa4, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                                                call(0x0f4240, sload(0x04), 0, 0x80, 0x44, 0x80, 0x20)
                                                                                                                                                if call(0x0f4240, sload(0x04), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                                                    if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                                                                                        if iszero(eq(0x01, 0)) { revert(0, 0); } else {
                                                                                                                                                            mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x80, caller())
                                                                                                                                                            mstore(0xa0, mload(0x0100))
                                                                                                                                                            mstore(0xc0, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                                                            log1(0x80, 0x60, 0xec43a82fae8c251f7aae4f79accf59c765bd798d597ccfd95beef20bf096cc9e)
                                                                                                                                                            mstore(0x80, div(mul(div(mul(mload(0x0100), 0x26f2), 0x2710), sload(0)), add(sload(0x01), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                                                            return(0x80, 0x20)
                                                                                                                                                            mstore(0x80, 0x1078b53300000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x84, 0x12)
                                                                                                                                                            mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                                                                                                        }
                                                                                                                                                    }
                                                                                                                                                }
                                                                                                                                            }
                                                                                                                                        }
                                                                                                                                    }
                                                                                                                                }
                                                                                                                            }
                                                                                                                        }
                                                                                                                    }
                                                                                                                }
                                                                                                            }
                                                                                                        }
                                                                                                    }
                                                                                                }
                                                                                            }
                                                                                        }
                                                                                    }
                                                                                }
                                                                            }
                                                                        }
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_ce9c0bb7(uint256 arg0) public payable
            * @param                arg0 ["uint256", "bytes32", "int256"]
            */
            case 0xce9c0bb7 {
                if iszero(lt(calldatasize(), 0x24)) {
                    if eq(caller(), sload(0x08)) { revert(0x80, 0x04); } else {
                        mstore(0x80, 0x30cd747100000000000000000000000000000000000000000000000000000000)
                        if iszero(lt(0x2710, calldataload(0x04))) { revert(0, 0); } else {
                            mstore(0x80, 0xcd4e616700000000000000000000000000000000000000000000000000000000)
                            sstore(0x0a, calldataload(0x04))
                            mstore(0x80, calldataload(0x04))
                            log1(0x80, 0x20, 0xac9f8df6116458aab7d2642e648145d5f693b4d6a1f0dff57db25547224c8b55)
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_0902f1ac() public view returns (bytes memory)
            */
            case 0x0902f1ac {
                if iszero(lt(calldatasize(), 0x04)) { revert(0, 0); } else {
                    mstore(0x80, sload(0))
                    mstore(0xa0, sload(0x01))
                    return(0x80, 0x40)
                }
            }
            
            /*
            * @custom:signature    Unresolved_f5eb42dc(uint256 arg0) public view returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            */
            case 0xf5eb42dc {
                if iszero(lt(calldatasize(), 0x24)) { revert(0, 0); } else {
                    mstore(0, calldataload(0x04))
                    mstore(0x20, 0x03)
                    mstore(0x80, sload(sha3(0, 0x40)))
                    return(0x80, 0x20)
                }
            }
            default { revert(0, 0) }
        }
    }
}