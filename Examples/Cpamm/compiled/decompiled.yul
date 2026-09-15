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
                    tstore(0, 0x01)
                    mstore(0x0100, calldataload(0x04))
                    if lt(0, mload(0x0100)) {
                        if lt(0, sload(0x02)) {
                            if lt(0, sload(0x03)) {
                                if 0x2710 {
                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                    mstore(0x84, 0x12)
                                    if or(iszero(mload(0x0100)), eq(div(mul(mload(0x0100), 0x26f2), mload(0x0100)), 0x26f2)) {
                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                        mstore(0x84, 0x11)
                                        if iszero(lt(add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x02))) {
                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                            mstore(0x84, 0x11)
                                            if add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710)) {
                                                if or(iszero(sload(0x03)), eq(div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x03)), div(mul(mload(0x0100), 0x26f2), 0x2710))) {
                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                    mstore(0x84, 0x11)
                                                    if iszero(lt(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710))) {
                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                        mstore(0x84, 0x11)
                                                        if eq(0, eq(sload(0x07), 0)) {
                                                            if 0x2710 {
                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                mstore(0x84, 0x12)
                                                                if or(iszero(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710))), eq(div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x08)), sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710))), sload(0x08))) {
                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                    mstore(0x84, 0x11)
                                                                    if iszero(lt(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x08)), 0x2710))) { revert(0x80, 0x04); } else {
                                                                        mstore(0x80, 0xcd4e616700000000000000000000000000000000000000000000000000000000)
                                                                        if iszero(lt(div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710))), calldataload(0x24))) { revert(0x80, 0x04); } else {
                                                                            mstore(0x80, 0xbb2875c300000000000000000000000000000000000000000000000000000000)
                                                                            if lt(0, div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710)))) {
                                                                                if iszero(lt(mload(0x0100), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x08)), 0x2710))) {
                                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                    mstore(0x84, 0x11)
                                                                                    if iszero(lt(add(sload(0x02), sub(mload(0x0100), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x08)), 0x2710))), sload(0x02))) {
                                                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                        mstore(0x84, 0x11)
                                                                                        sstore(0x02, add(sload(0x02), sub(mload(0x0100), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x08)), 0x2710))))
                                                                                        if iszero(lt(sload(0x03), div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710))))) {
                                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                            mstore(0x84, 0x11)
                                                                                            sstore(0x03, sub(sload(0x03), div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710)))))
                                                                                            if iszero(lt(add(sload(0x09), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x08)), 0x2710)), sload(0x09))) {
                                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                mstore(0x84, 0x11)
                                                                                                sstore(0x09, add(sload(0x09), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), sload(0x08)), 0x2710)))
                                                                                                mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                                                mstore(0x84, caller())
                                                                                                mstore(0xa4, address())
                                                                                                mstore(0xc4, mload(0x0100))
                                                                                                call(0x0f4240, sload(0), 0, 0x80, 0x64, 0x80, 0x20)
                                                                                                if call(0x0f4240, sload(0), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                    if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), lt(returndatasize(), 0x40))) {
                                                                                                        if eq(or(iszero(returndatasize()), iszero(iszero(mload(0x80)))), 0x01) { revert(0x80, 0x04); } else {
                                                                                                            mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                            mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                                                                                                            mstore(0x84, caller())
                                                                                                            mstore(0xa4, div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                            call(0x0f4240, sload(0x01), 0, 0x80, 0x44, 0x80, 0x20)
                                                                                                            if call(0x0f4240, sload(0x01), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), lt(returndatasize(), 0x40))) {
                                                                                                                    if eq(or(iszero(returndatasize()), iszero(iszero(mload(0x80)))), 0x01) { revert(0x80, 0x04); } else {
                                                                                                                        mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                        mstore(0x80, caller())
                                                                                                                        mstore(0xa0, mload(0x0100))
                                                                                                                        mstore(0xc0, div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                        log1(0x80, 0x60, 0x268d208c45ec3d7213f545c4402b1bc7f11b332757a4e0d84ff4d37b90db1fca)
                                                                                                                        tstore(0, 0)
                                                                                                                        mstore(0x80, div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                        return(0x80, 0x20)
                                                                                                                        mstore(0x80, 0x1078b53300000000000000000000000000000000000000000000000000000000)
                                                                                                                        if 0x2710 {
                                                                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                            mstore(0x84, 0x12)
                                                                                                                            if or(iszero(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710))), eq(div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), 0), sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710))), 0)) {
                                                                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                mstore(0x84, 0x11)
                                                                                                                                if iszero(lt(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), 0), 0x2710))) { revert(0x80, 0x04); } else {
                                                                                                                                    mstore(0x80, 0xcd4e616700000000000000000000000000000000000000000000000000000000)
                                                                                                                                    if iszero(lt(div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710))), calldataload(0x24))) { revert(0x80, 0x04); } else {
                                                                                                                                        mstore(0x80, 0xbb2875c300000000000000000000000000000000000000000000000000000000)
                                                                                                                                        if lt(0, div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710)))) {
                                                                                                                                            if iszero(lt(mload(0x0100), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), 0), 0x2710))) {
                                                                                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                                mstore(0x84, 0x11)
                                                                                                                                                if iszero(lt(add(sload(0x02), sub(mload(0x0100), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), 0), 0x2710))), sload(0x02))) {
                                                                                                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                                    mstore(0x84, 0x11)
                                                                                                                                                    sstore(0x02, add(sload(0x02), sub(mload(0x0100), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), 0), 0x2710))))
                                                                                                                                                    if iszero(lt(sload(0x03), div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710))))) {
                                                                                                                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                                        mstore(0x84, 0x11)
                                                                                                                                                        sstore(0x03, sub(sload(0x03), div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710)))))
                                                                                                                                                        if iszero(lt(add(sload(0x09), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), 0), 0x2710)), sload(0x09))) {
                                                                                                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x84, 0x11)
                                                                                                                                                            sstore(0x09, add(sload(0x09), div(mul(sub(mload(0x0100), div(mul(mload(0x0100), 0x26f2), 0x2710)), 0), 0x2710)))
                                                                                                                                                            mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                                                                                                            mstore(0x84, caller())
                                                                                                                                                            mstore(0xa4, address())
                                                                                                                                                            mstore(0xc4, mload(0x0100))
                                                                                                                                                            call(0x0f4240, sload(0), 0, 0x80, 0x64, 0x80, 0x20)
                                                                                                                                                            if call(0x0f4240, sload(0), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                                                                if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), lt(returndatasize(), 0x40))) {
                                                                                                                                                                    if eq(or(iszero(returndatasize()), iszero(iszero(mload(0x80)))), 0x01) { revert(0x80, 0x04); } else {
                                                                                                                                                                        mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                        mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                        mstore(0x84, caller())
                                                                                                                                                                        mstore(0xa4, div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                                                                        call(0x0f4240, sload(0x01), 0, 0x80, 0x44, 0x80, 0x20)
                                                                                                                                                                        if call(0x0f4240, sload(0x01), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                                                                                                                                                            if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), lt(returndatasize(), 0x40))) {
                                                                                                                                                                                if eq(or(iszero(returndatasize()), iszero(iszero(mload(0x80)))), 0x01) { revert(0, 0); } else {
                                                                                                                                                                                    mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                                                                                                                    mstore(0x80, caller())
                                                                                                                                                                                    mstore(0xa0, mload(0x0100))
                                                                                                                                                                                    mstore(0xc0, div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710))))
                                                                                                                                                                                    log1(0x80, 0x60, 0x268d208c45ec3d7213f545c4402b1bc7f11b332757a4e0d84ff4d37b90db1fca)
                                                                                                                                                                                    tstore(0, 0)
                                                                                                                                                                                    mstore(0x80, div(mul(sload(0x03), div(mul(mload(0x0100), 0x26f2), 0x2710)), add(sload(0x02), div(mul(mload(0x0100), 0x26f2), 0x2710))))
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
                    tstore(0, 0x01)
                    if iszero(eq(sload(0x07), 0)) {
                        if eq(caller(), sload(0x07)) { revert(0x80, 0x04); } else {
                            mstore(0x80, 0x30cd747100000000000000000000000000000000000000000000000000000000)
                            sstore(0x09, 0)
                            sstore(0x0a, 0)
                            mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                            mstore(0x84, caller())
                            mstore(0xa4, sload(0x09))
                            call(0x0f4240, sload(0), 0, 0x80, 0x44, 0x80, 0x20)
                            if call(0x0f4240, sload(0), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), lt(returndatasize(), 0x40))) {
                                    if eq(or(iszero(returndatasize()), iszero(iszero(mload(0x80)))), 0x01) { revert(0x80, 0x04); } else {
                                        mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                        mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                                        mstore(0x84, caller())
                                        mstore(0xa4, sload(0x0a))
                                        call(0x0f4240, sload(0x01), 0, 0x80, 0x44, 0x80, 0x20)
                                        if call(0x0f4240, sload(0x01), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                            if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), lt(returndatasize(), 0x40))) {
                                                if eq(or(iszero(returndatasize()), iszero(iszero(mload(0x80)))), 0x01) { revert(0x80, 0x04); } else {
                                                    mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                    mstore(0x80, caller())
                                                    mstore(0xa0, sload(0x09))
                                                    mstore(0xc0, sload(0x0a))
                                                    log1(0x80, 0x60, 0xd24ccccf373129a9579bb9f5edc41c09218d54ae950e90b4d5ca2927b7c29b11)
                                                    tstore(0, 0)
                                                    mstore(0x80, sload(0x09))
                                                    mstore(0xa0, sload(0x0a))
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
            * @custom:signature    Unresolved_1ad8b03b() public pure
            */
            case 0x1ad8b03b {
            }
            
            /*
            * @custom:signature    Unresolved_9cd441da() public pure
            */
            case 0x9cd441da {
            }
            
            /*
            * @custom:signature    Unresolved_9c8f9f23() public pure
            */
            case 0x9c8f9f23 {
            }
            
            /*
            * @custom:signature    Unresolved_f46901ed() public pure
            */
            case 0xf46901ed {
            }
            
            /*
            * @custom:signature    Unresolved_21d2da23() public pure
            */
            case 0x21d2da23 {
            }
            
            /*
            * @custom:signature    Unresolved_ce9c0bb7() public pure
            */
            case 0xce9c0bb7 {
            }
            
            /*
            * @custom:signature    Unresolved_0902f1ac() public pure
            */
            case 0x0902f1ac {
            }
            
            /*
            * @custom:signature    Unresolved_f5eb42dc() public pure
            */
            case 0xf5eb42dc {
            }
            default { revert(0, 0) }
        }
    }
}