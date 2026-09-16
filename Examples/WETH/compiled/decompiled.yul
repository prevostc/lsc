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
            * @custom:signature    Unresolved_a9059cbb(uint256 arg0, uint256 arg1) public returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            * @param                arg1 ["uint256", "bytes32", "int256"]
            */
            case 0xa9059cbb {
                if iszero(lt(calldatasize(), 0x44)) {
                    if iszero(callvalue()) { revert(0, 0); } else {
                        mstore(0, caller())
                        mstore(0x20, 0)
                        if iszero(lt(sload(sha3(0, 0x40)), calldataload(0x24))) { revert(0x80, 0x04); } else {
                            mstore(0x80, 0xf4d678b800000000000000000000000000000000000000000000000000000000)
                            if iszero(lt(sload(sha3(0, 0x40)), calldataload(0x24))) {
                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                mstore(0x84, 0x11)
                                mstore(0, caller())
                                mstore(0x20, 0)
                                sstore(sha3(0, 0x40), sub(sload(sha3(0, 0x40)), calldataload(0x24)))
                                mstore(0, calldataload(0x04))
                                mstore(0x20, 0)
                                if iszero(lt(add(sload(sha3(0, 0x40)), calldataload(0x24)), sload(sha3(0, 0x40)))) { revert(0, 0); } else {
                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                    mstore(0x84, 0x11)
                                    mstore(0, calldataload(0x04))
                                    mstore(0x20, 0)
                                    sstore(sha3(0, 0x40), add(sload(sha3(0, 0x40)), calldataload(0x24)))
                                    mstore(0x80, caller())
                                    mstore(0xa0, calldataload(0x04))
                                    mstore(0xc0, calldataload(0x24))
                                    log1(0x80, 0x60, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef)
                                    mstore(0x80, 0x01)
                                    return(0x80, 0x20)
                                }
                            }
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_2e1a7d4d(uint256 arg0) public
            * @param                arg0 ["uint256", "bytes32", "int256"]
            */
            case 0x2e1a7d4d {
                if iszero(lt(calldatasize(), 0x24)) {
                    if iszero(callvalue()) { revert(0, 0); } else {
                        tstore(0, 0x01)
                        mstore(0, caller())
                        mstore(0x20, 0)
                        if iszero(lt(sload(sha3(0, 0x40)), calldataload(0x04))) { revert(0x80, 0x04); } else {
                            mstore(0x80, 0xf4d678b800000000000000000000000000000000000000000000000000000000)
                            if iszero(lt(sload(sha3(0, 0x40)), calldataload(0x04))) {
                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                mstore(0x84, 0x11)
                                mstore(0, caller())
                                mstore(0x20, 0)
                                sstore(sha3(0, 0x40), sub(sload(sha3(0, 0x40)), calldataload(0x04)))
                                if iszero(lt(sload(0x02), calldataload(0x04))) {
                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                    mstore(0x84, 0x11)
                                    sstore(0x02, sub(sload(0x02), calldataload(0x04)))
                                    mstore(0x80, caller())
                                    mstore(0xa0, 0)
                                    mstore(0xc0, calldataload(0x04))
                                    log1(0x80, 0x60, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef)
                                    call(0x0f4240, caller(), calldataload(0x04), 0, 0, 0, 0)
                                    if eq(call(0x0f4240, caller(), calldataload(0x04), 0, 0, 0, 0), 0x01) { revert(0, 0); } else {
                                        mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                        mstore(0x80, caller())
                                        mstore(0xa0, calldataload(0x04))
                                        log1(0x80, 0x40, 0x7fcf532c15f0a6db0bd6d0e038bea71d30d808c7d98cb3bf7268a95bf5081b65)
                                        tstore(0, 0)
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_dd62ed3e(uint256 arg0, uint256 arg1) public view returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            * @param                arg1 ["uint256", "bytes32", "int256"]
            */
            case 0xdd62ed3e {
                if iszero(lt(calldatasize(), 0x44)) {
                    if iszero(callvalue()) { revert(0, 0); } else {
                        mstore(0, calldataload(0x04))
                        mstore(0x20, 0x01)
                        mstore(0x20, sha3(0, 0x40))
                        mstore(0, calldataload(0x24))
                        mstore(0x80, sload(sha3(0, 0x40)))
                        return(0x80, 0x20)
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_23b872dd(uint256 arg0, uint256 arg1, uint256 arg2) public returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            * @param                arg1 ["uint256", "bytes32", "int256"]
            * @param                arg2 ["uint256", "bytes32", "int256"]
            */
            case 0x23b872dd {
                if iszero(lt(calldatasize(), 0x64)) {
                    if iszero(callvalue()) { revert(0, 0); } else {
                        mstore(0, calldataload(0x04))
                        mstore(0x20, 0x01)
                        mstore(0x20, sha3(0, 0x40))
                        mstore(0, caller())
                        if iszero(lt(sload(sha3(0, 0x40)), calldataload(0x44))) { revert(0x80, 0x04); } else {
                            mstore(0x80, 0x13be252b00000000000000000000000000000000000000000000000000000000)
                            mstore(0, calldataload(0x04))
                            mstore(0x20, 0)
                            if iszero(lt(sload(sha3(0, 0x40)), calldataload(0x44))) { revert(0x80, 0x04); } else {
                                mstore(0x80, 0xf4d678b800000000000000000000000000000000000000000000000000000000)
                                if iszero(lt(sload(sha3(0, 0x40)), calldataload(0x44))) {
                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                    mstore(0x84, 0x11)
                                    mstore(0, calldataload(0x04))
                                    mstore(0x20, 0x01)
                                    mstore(0x20, sha3(0, 0x40))
                                    mstore(0, caller())
                                    sstore(sha3(0, 0x40), sub(sload(sha3(0, 0x40)), calldataload(0x44)))
                                    if iszero(lt(sload(sha3(0, 0x40)), calldataload(0x44))) {
                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                        mstore(0x84, 0x11)
                                        mstore(0, calldataload(0x04))
                                        mstore(0x20, 0)
                                        sstore(sha3(0, 0x40), sub(sload(sha3(0, 0x40)), calldataload(0x44)))
                                        mstore(0, calldataload(0x24))
                                        mstore(0x20, 0)
                                        if iszero(lt(add(sload(sha3(0, 0x40)), calldataload(0x44)), sload(sha3(0, 0x40)))) { revert(0, 0); } else {
                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                            mstore(0x84, 0x11)
                                            mstore(0, calldataload(0x24))
                                            mstore(0x20, 0)
                                            sstore(sha3(0, 0x40), add(sload(sha3(0, 0x40)), calldataload(0x44)))
                                            mstore(0x80, calldataload(0x04))
                                            mstore(0xa0, calldataload(0x24))
                                            mstore(0xc0, calldataload(0x44))
                                            log1(0x80, 0x60, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef)
                                            mstore(0x80, 0x01)
                                            return(0x80, 0x20)
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_095ea7b3(uint256 arg0, uint256 arg1) public returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            * @param                arg1 ["uint256", "bytes32", "int256"]
            */
            case 0x095ea7b3 {
                if iszero(lt(calldatasize(), 0x44)) {
                    if iszero(callvalue()) { revert(0, 0); } else {
                        mstore(0, caller())
                        mstore(0x20, 0x01)
                        mstore(0x20, sha3(0, 0x40))
                        mstore(0, calldataload(0x04))
                        sstore(sha3(0, 0x40), calldataload(0x24))
                        mstore(0x80, caller())
                        mstore(0xa0, calldataload(0x04))
                        mstore(0xc0, calldataload(0x24))
                        log1(0x80, 0x60, 0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925)
                        mstore(0x80, 0x01)
                        return(0x80, 0x20)
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_70a08231(uint256 arg0) public view returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            */
            case 0x70a08231 {
                if iszero(lt(calldatasize(), 0x24)) {
                    if iszero(callvalue()) { revert(0, 0); } else {
                        mstore(0, calldataload(0x04))
                        mstore(0x20, 0)
                        mstore(0x80, sload(sha3(0, 0x40)))
                        return(0x80, 0x20)
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_d0e30db0() public payable
            */
            case 0xd0e30db0 {
                if iszero(lt(calldatasize(), 0x04)) { revert(0, 0); } else {
                    if iszero(lt(selfbalance(), callvalue())) { revert(0, 0); } else {
                        if iszero(lt(add(sload(0x02), callvalue()), sload(0x02))) {
                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                            mstore(0x84, 0x11)
                            sstore(0x02, add(sload(0x02), callvalue()))
                            mstore(0, caller())
                            mstore(0x20, 0)
                            if iszero(lt(add(sload(sha3(0, 0x40)), callvalue()), sload(sha3(0, 0x40)))) {
                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                mstore(0x84, 0x11)
                                mstore(0, caller())
                                mstore(0x20, 0)
                                sstore(sha3(0, 0x40), add(sload(sha3(0, 0x40)), callvalue()))
                                mstore(0x80, 0)
                                mstore(0xa0, caller())
                                mstore(0xc0, callvalue())
                                log1(0x80, 0x60, 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef)
                                mstore(0x80, caller())
                                mstore(0xa0, callvalue())
                                log1(0x80, 0x40, 0xe1fffcc4923d04b559f4d29a8bfc6cda04eb5b0d3c460751c2402c5c5cc9109c)
                            }
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_18160ddd() public view returns (uint256)
            */
            case 0x18160ddd {
                if iszero(lt(calldatasize(), 0x04)) { revert(0, 0); } else {
                    if iszero(callvalue()) { revert(0, 0); } else {
                        mstore(0x80, sload(0x02))
                        return(0x80, 0x20)
                    }
                }
            }
            default { revert(0, 0) }
        }
    }
}