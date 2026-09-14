// SPDX-License-Identifier: MIT
pragma solidity >=0.8.0;

/// @title            Decompiled Contract
/// @author           Jonathan Becker <jonathan@jbecker.dev>
/// @custom:version   heimdall-rs v0.9.2
///
/// @notice           This contract was decompiled using the heimdall-rs decompiler.
///                     It was generated directly by tracing the EVM opcodes from this contract.
///                     As a result, it may not compile or even be valid solidity code.
///                     Despite this, it should be obvious what each function does. Overall
///                     logic should have been preserved throughout decompiling.
///
/// @custom:github    You can find the open-source decompiler here:
///                       https://heimdall.rs

contract DecompiledContract {
    uint256 public get;
    
    event Incremented(uint256);
    error Zero();
    
    /// @custom:selector    0x2baeceb7
    /// @custom:signature   decrement() public payable
    function decrement() public payable {
        if (0 == (get == 0)) {
            if (!get < 0x01) {
                get = get - 0x01;
                get = 0;
            }
        }
    }
    
    /// @custom:selector    0x03df179c
    /// @custom:signature   incrementBy(uint256 arg0) public payable
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function incrementBy(uint256 arg0) public payable {
        require(!(msg.data.length < 0x24), CustomError_f4560403());
        require(!(arg0 == 0), CustomError_f4560403());
        require(!((get + arg0) < get), CustomError_f4560403());
        get = get + arg0;
        emit Incremented(arg0);
    }
    
    /// @custom:selector    0xd09de08a
    /// @custom:signature   increment() public payable
    function increment() public payable {
        if (!(get + 0x01) < get) {
            get = get + 0x01;
            emit Incremented(0x01);
        }
    }
}