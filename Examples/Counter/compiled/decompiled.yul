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
            * @custom:signature    decrement() public payable
            */
            case 0x2baeceb7 {
                if iszero(lt(calldatasize(), 0x04)) { revert(0, 0); } else {
                    if eq(0, eq(sload(0), 0)) {
                        if iszero(lt(sload(0), 0x01)) {
                            sstore(0, sub(sload(0), 0x01))
                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                            mstore(0x84, 0x11)
                            sstore(0, 0)
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    incrementBy(uint256 arg0) public payable
            * @param                arg0 ["uint256", "bytes32", "int256"]
            */
            case 0x03df179c {
                if iszero(lt(calldatasize(), 0x24)) {
                    if iszero(eq(calldataload(0x04), 0)) {
                        if iszero(lt(add(sload(0), calldataload(0x04)), sload(0))) { revert(0, 0); } else {
                            mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                            mstore(0x84, 0x11)
                            sstore(0, add(sload(0), calldataload(0x04)))
                            mstore(0x80, calldataload(0x04))
                            log1(0x80, 0x20, 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84)
                            mstore(0x80, 0xf456040300000000000000000000000000000000000000000000000000000000)
                        }
                    }
                }
            }
            
            /*
            * @custom:signature    increment() public payable
            */
            case 0xd09de08a {
                if iszero(lt(calldatasize(), 0x04)) { revert(0, 0); } else {
                    if iszero(lt(add(sload(0), 0x01), sload(0))) {
                        mstore(0x80, 0x4e487b7100000000000000000000000000000000000000000000000000000000)
                        mstore(0x84, 0x11)
                        sstore(0, add(sload(0), 0x01))
                        mstore(0x80, 0x01)
                        log1(0x80, 0x20, 0x20d8a6f5a693f9d1d627a598e8820f7a55ee74c183aa8f1a30e8d4e8dd9a8d84)
                    }
                }
            }
            
            /*
            * @custom:signature    get() public view returns (uint256)
            */
            case 0x6d4ce63c {
                if iszero(lt(calldatasize(), 0x04)) { revert(0, 0); } else {
                    mstore(0x80, sload(0))
                    return(0x80, 0x20)
                }
            }
            default { revert(0, 0) }
        }
    }
}