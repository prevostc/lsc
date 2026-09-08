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
            * @custom:signature    previewRedeem(uint256 arg0) public view returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            */
            case 0x4cdad506 {
                if iszero(lt(calldatasize(), 0x24)) {
                    if sload(0x01) {
                        if or(iszero(sload(0)), eq(div(mul(sload(0), calldataload(0x04)), sload(0)), calldataload(0x04))) { revert(0, 0); } else {
                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                            mstore(0x84, 0x11)
                            mstore(0x80, div(mul(sload(0), calldataload(0x04)), sload(0x01)))
                            return(0x80, 0x20)
                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                            mstore(0x84, 0x12)
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    pause() public payable
            */
            case 0x8456cb59 {
                if iszero(lt(calldatasize(), 0x04)) { revert(0, 0); } else {
                    if eq(caller(), sload(0x04)) { revert(0x80, 0x04); } else {
                        mstore(0x80, 0x30cd747100000000000000000000000000000000000000000000000000000000)
                        sstore(0x03, 0x01)
                        log1(0x80, 0, 0x9e87fac88ff661f02d44f95383c817fece4bce600a3dab7a54406878b965e752)
                    }
                }
            }
            
            /*
            * @custom:signature    Unresolved_67dda112() public view returns (uint256)
            */
            case 0x67dda112 {
                if iszero(lt(calldatasize(), 0x04)) { revert(0, 0); } else {
                    mstore(0x80, sload(0x03))
                    return(0x80, 0x20)
                }
            }
            
            /*
            * @custom:signature    previewDeposit(uint256 arg0) public view returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            */
            case 0xef8b30f7 {
                if iszero(lt(calldatasize(), 0x24)) {
                    if eq(0, eq(sload(0x01), 0)) {
                        if sload(0) {
                            if or(iszero(sload(0x01)), eq(div(mul(sload(0x01), calldataload(0x04)), sload(0x01)), calldataload(0x04))) { revert(0, 0); } else {
                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                mstore(0x84, 0x11)
                                mstore(0x80, div(mul(sload(0x01), calldataload(0x04)), sload(0)))
                                return(0x80, 0x20)
                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                mstore(0x84, 0x12)
                                mstore(0x80, calldataload(0x04))
                                return(0x80, 0x20)
                            }
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    withdraw(uint256 arg0) public payable returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            */
            case 0x2e1a7d4d {
                if iszero(lt(calldatasize(), 0x24)) {
                    if eq(sload(0x03), 0) {
                        if lt(0, calldataload(0x04)) {
                            mstore(0, caller())
                            mstore(0x20, 0x02)
                            if iszero(lt(sload(sha3(0, 0x40)), calldataload(0x04))) { revert(0x80, 0x04); } else {
                                mstore(0x80, 0x3999656700000000000000000000000000000000000000000000000000000000)
                                if sload(0x01) {
                                    if or(iszero(sload(0)), eq(div(mul(sload(0), calldataload(0x04)), sload(0)), calldataload(0x04))) {
                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                        mstore(0x84, 0x11)
                                        if lt(0, div(mul(sload(0), calldataload(0x04)), sload(0x01))) {
                                            if iszero(lt(sload(sha3(0, 0x40)), calldataload(0x04))) {
                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                mstore(0x84, 0x11)
                                                mstore(0, caller())
                                                mstore(0x20, 0x02)
                                                sstore(sha3(0, 0x40), sub(sload(sha3(0, 0x40)), calldataload(0x04)))
                                                if iszero(lt(sload(0x01), calldataload(0x04))) {
                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                    mstore(0x84, 0x11)
                                                    sstore(0x01, sub(sload(0x01), calldataload(0x04)))
                                                    if iszero(lt(sload(0), div(mul(sload(0), calldataload(0x04)), sload(0x01)))) {
                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                        mstore(0x84, 0x11)
                                                        sstore(0, sub(sload(0), div(mul(sload(0), calldataload(0x04)), sload(0x01))))
                                                        mstore(0x80, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
                                                        mstore(0x84, caller())
                                                        mstore(0xa4, div(mul(sload(0), calldataload(0x04)), sload(0x01)))
                                                        call(0x0f4240, sload(0x05), 0, 0x80, 0x44, 0x80, 0x20)
                                                        if call(0x0f4240, sload(0x05), 0, 0x80, 0x44, 0x80, 0x20) { revert(0, 0); } else {
                                                            if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                if iszero(eq(0x01, 0)) { revert(0, 0); } else {
                                                                    mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                    mstore(0x80, caller())
                                                                    mstore(0xa0, div(mul(sload(0), calldataload(0x04)), sload(0x01)))
                                                                    mstore(0xc0, calldataload(0x04))
                                                                    log1(0x80, 0x60, 0xf279e6a1f5e320cca91135676d9cb6e44ca8a08c0b88342bcdb1144f6511b568)
                                                                    mstore(0x80, div(mul(sload(0), calldataload(0x04)), sload(0x01)))
                                                                    return(0x80, 0x20)
                                                                    mstore(0x80, 0x32d971dc00000000000000000000000000000000000000000000000000000000)
                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                    mstore(0x84, 0x12)
                                                                    mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                                                                    mstore(0x80, 0x9e87fac800000000000000000000000000000000000000000000000000000000)
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
            * @custom:signature    unpause() public payable
            */
            case 0x3f4ba83a {
                if iszero(lt(calldatasize(), 0x04)) { revert(0, 0); } else {
                    if eq(caller(), sload(0x04)) { revert(0x80, 0x04); } else {
                        mstore(0x80, 0x30cd747100000000000000000000000000000000000000000000000000000000)
                        sstore(0x03, 0)
                        log1(0x80, 0, 0xa45f47fdea8a1efdd9029a5691c7f759c32b7c698632b563573e155625d16933)
                    }
                }
            }
            
            /*
            * @custom:signature    deposit(uint256 arg0) public payable returns (uint256)
            * @param                arg0 ["uint256", "bytes32", "int256"]
            */
            case 0xb6b55f25 {
                if iszero(lt(calldatasize(), 0x24)) {
                    if eq(sload(0x03), 0) { revert(0x80, 0x04); } else {
                        mstore(0x80, 0x9e87fac800000000000000000000000000000000000000000000000000000000)
                        if lt(0, calldataload(0x04)) {
                            if eq(0, eq(sload(0x01), 0)) {
                                if sload(0) {
                                    if or(iszero(sload(0x01)), eq(div(mul(sload(0x01), calldataload(0x04)), sload(0x01)), calldataload(0x04))) {
                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                        mstore(0x84, 0x11)
                                        if lt(0, div(mul(sload(0x01), calldataload(0x04)), sload(0))) {
                                            mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                            mstore(0x84, caller())
                                            mstore(0xa4, address())
                                            mstore(0xc4, calldataload(0x04))
                                            call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20)
                                            if call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                    if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                        mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                        if iszero(lt(add(sload(0), calldataload(0x04)), sload(0))) {
                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                            mstore(0x84, 0x11)
                                                            sstore(0, add(sload(0), calldataload(0x04)))
                                                            if iszero(lt(add(div(mul(sload(0x01), calldataload(0x04)), sload(0)), sload(0x01)), div(mul(sload(0x01), calldataload(0x04)), sload(0)))) {
                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                mstore(0x84, 0x11)
                                                                sstore(0x01, add(div(mul(sload(0x01), calldataload(0x04)), sload(0)), sload(0x01)))
                                                                mstore(0, caller())
                                                                mstore(0x20, 0x02)
                                                                if iszero(lt(add(div(mul(sload(0x01), calldataload(0x04)), sload(0)), sload(sha3(0, 0x40))), div(mul(sload(0x01), calldataload(0x04)), sload(0)))) { revert(0x80, 0x04); } else {
                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                    mstore(0x84, 0x11)
                                                                    mstore(0, caller())
                                                                    mstore(0x20, 0x02)
                                                                    sstore(sha3(0, 0x40), add(div(mul(sload(0x01), calldataload(0x04)), sload(0)), sload(sha3(0, 0x40))))
                                                                    mstore(0x80, caller())
                                                                    mstore(0xa0, calldataload(0x04))
                                                                    mstore(0xc0, div(mul(sload(0x01), calldataload(0x04)), sload(0)))
                                                                    log1(0x80, 0x60, 0x90890809c654f11d6e72a28fa60149770a0d11ec6c92319d6ceb2bb0a4ea1a15)
                                                                    mstore(0x80, div(mul(sload(0x01), calldataload(0x04)), sload(0)))
                                                                    return(0x80, 0x20)
                                                                    mstore(0x80, 0x9811e0c700000000000000000000000000000000000000000000000000000000)
                                                                    mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                    mstore(0x84, 0x12)
                                                                    if lt(0, calldataload(0x04)) {
                                                                        mstore(0x80, 0x23b872dd00000000000000000000000000000000000000000000000000000000)
                                                                        mstore(0x84, caller())
                                                                        mstore(0xa4, address())
                                                                        mstore(0xc4, calldataload(0x04))
                                                                        call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20)
                                                                        if call(0x0f4240, sload(0x05), 0, 0x80, 0x64, 0x80, 0x20) { revert(0, 0); } else {
                                                                            if or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x80), 0x01))) {
                                                                                if iszero(eq(0x01, 0)) { revert(0x80, 0x04); } else {
                                                                                    mstore(0x80, 0x90b8ec1800000000000000000000000000000000000000000000000000000000)
                                                                                    if iszero(lt(add(sload(0), calldataload(0x04)), sload(0))) {
                                                                                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                        mstore(0x84, 0x11)
                                                                                        sstore(0, add(sload(0), calldataload(0x04)))
                                                                                        if iszero(lt(add(calldataload(0x04), sload(0x01)), calldataload(0x04))) {
                                                                                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                            mstore(0x84, 0x11)
                                                                                            sstore(0x01, add(calldataload(0x04), sload(0x01)))
                                                                                            mstore(0, caller())
                                                                                            mstore(0x20, 0x02)
                                                                                            if iszero(lt(add(calldataload(0x04), sload(sha3(0, 0x40))), calldataload(0x04))) { revert(0, 0); } else {
                                                                                                mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                                                                                                mstore(0x84, 0x11)
                                                                                                mstore(0, caller())
                                                                                                mstore(0x20, 0x02)
                                                                                                sstore(sha3(0, 0x40), add(calldataload(0x04), sload(sha3(0, 0x40))))
                                                                                                mstore(0x80, caller())
                                                                                                mstore(0xa0, calldataload(0x04))
                                                                                                mstore(0xc0, calldataload(0x04))
                                                                                                log1(0x80, 0x60, 0x90890809c654f11d6e72a28fa60149770a0d11ec6c92319d6ceb2bb0a4ea1a15)
                                                                                                mstore(0x80, calldataload(0x04))
                                                                                                return(0x80, 0x20)
                                                                                                mstore(0x80, 0x9811e0c700000000000000000000000000000000000000000000000000000000)
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
            * @custom:signature    decimals() public view returns (uint256)
            */
            case 0x313ce567 {
                if iszero(lt(calldatasize(), 0x04)) { revert(0, 0); } else {
                    mstore(0x80, sload(0x06))
                    return(0x80, 0x20)
                }
            }
            default { revert(0, 0) }
        }
    }
}