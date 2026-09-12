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
    uint256 public unresolved_6d4ce63c;
    
    event Event_20d8a6f5();
    error CustomError_00000000();
    
    /// @custom:selector    0x2baeceb7
    /// @custom:signature   Unresolved_2baeceb7() public payable
    function Unresolved_2baeceb7() public payable {
        if (0 == (unresolved_6d4ce63c == 0)) {
            if (!unresolved_6d4ce63c < 0x01) {
                unresolved_6d4ce63c = unresolved_6d4ce63c - 0x01;
                unresolved_6d4ce63c = 0;
            }
        }
    }
    
    /// @custom:selector    0x03df179c
    /// @custom:signature   Unresolved_03df179c(uint256 arg0) public payable
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_03df179c(uint256 arg0) public payable {
        require(!(msg.data.length < 0x24), CustomError_f4560403());
        require(!(arg0 == 0), CustomError_f4560403());
        require(!((unresolved_6d4ce63c + arg0) < unresolved_6d4ce63c), CustomError_f4560403());
        unresolved_6d4ce63c = unresolved_6d4ce63c + arg0;
        emit Event_20d8a6f5(arg0);
    }
    
    /// @custom:selector    0xd09de08a
    /// @custom:signature   Unresolved_d09de08a() public payable
    function Unresolved_d09de08a() public payable {
        if (!(unresolved_6d4ce63c + 0x01) < unresolved_6d4ce63c) {
            unresolved_6d4ce63c = unresolved_6d4ce63c + 0x01;
            emit Event_20d8a6f5(0x01);
        }
    }
}