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
    mapping(bytes32 => bytes32) storage_map_a;
    mapping(bytes32 => bytes32) storage_map_d;
    bytes32 store_c;
    uint256 public unresolved_18160ddd;
    
    event Event_8c5be1e5();
    error CustomError_00000000();
    event Event_ddf252ad();
    
    /// @custom:selector    0x42966c68
    /// @custom:signature   Unresolved_42966c68(uint256 arg0) public payable
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_42966c68(uint256 arg0) public payable {
        require(!(msg.data.length < 0x24), CustomError_f4d678b8());
        address var_a = msg.sender;
        require(0 == (!storage_map_a[var_a] < arg0), CustomError_f4d678b8());
        require(!storage_map_a[var_a] < arg0);
        var_a = msg.sender;
        storage_map_a[var_a] = storage_map_a[var_a] - arg0;
        require(!unresolved_18160ddd < arg0);
        unresolved_18160ddd = unresolved_18160ddd - arg0;
        emit Event_ddf252ad(msg.sender, 0, arg0);
    }
    
    /// @custom:selector    0xa9059cbb
    /// @custom:signature   Unresolved_a9059cbb(uint256 arg0, uint256 arg1) public payable
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_a9059cbb(uint256 arg0, uint256 arg1) public payable {
        require(!(msg.data.length < 0x44), CustomError_f4d678b8());
        address var_a = msg.sender;
        require(!(storage_map_a[var_a] < arg1), CustomError_f4d678b8());
        require(!storage_map_a[var_a] < arg1);
        var_a = msg.sender;
        storage_map_a[var_a] = storage_map_a[var_a] - arg1;
        var_a = arg0;
        require(!(storage_map_a[var_a] + arg1) < storage_map_a[var_a]);
        var_a = arg0;
        storage_map_a[var_a] = storage_map_a[var_a] + arg1;
        emit Event_ddf252ad(msg.sender, arg0, arg1);
    }
    
    /// @custom:selector    0x40c10f19
    /// @custom:signature   Unresolved_40c10f19(uint256 arg0, uint256 arg1) public payable
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_40c10f19(uint256 arg0, uint256 arg1) public payable {
        require(!(msg.data.length < 0x44), CustomError_30cd7471());
        require(msg.sender == store_c, CustomError_30cd7471());
        require(!(unresolved_18160ddd + arg1) < unresolved_18160ddd);
        unresolved_18160ddd = unresolved_18160ddd + arg1;
        uint256 var_c = arg0;
        require(!(storage_map_d[var_c] + arg1) < storage_map_d[var_c]);
        var_c = arg0;
        storage_map_d[var_c] = storage_map_d[var_c] + arg1;
        emit Event_ddf252ad(0, arg0, arg1);
    }
    
    /// @custom:selector    0xdd62ed3e
    /// @custom:signature   Unresolved_dd62ed3e(uint256 arg0, uint256 arg1) public view returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_dd62ed3e(uint256 arg0, uint256 arg1) public view returns (uint256) {
        require(!msg.data.length < 0x44);
        uint256 var_a = arg0;
        var_a = arg1;
        return storage_map_a[var_a];
    }
    
    /// @custom:selector    0x23b872dd
    /// @custom:signature   Unresolved_23b872dd(uint256 arg0, uint256 arg1, uint256 arg2) public payable
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    /// @param              arg2 ["uint256", "bytes32", "int256"]
    function Unresolved_23b872dd(uint256 arg0, uint256 arg1, uint256 arg2) public payable {
        require(!(msg.data.length < 0x64), CustomError_13be252b());
        uint256 var_a = arg0;
        var_a = msg.sender;
        require(!(storage_map_a[var_a] < arg2), CustomError_13be252b());
        var_a = arg0;
        require(!(storage_map_a[var_a] < arg2), CustomError_f4d678b8());
        require(!storage_map_a[var_a] < arg2);
        var_a = arg0;
        var_a = msg.sender;
        storage_map_a[var_a] = storage_map_a[var_a] - arg2;
        require(!storage_map_a[var_a] < arg2);
        var_a = arg0;
        storage_map_a[var_a] = storage_map_a[var_a] - arg2;
        var_a = arg1;
        require(!(storage_map_a[var_a] + arg2) < storage_map_a[var_a]);
        var_a = arg1;
        storage_map_a[var_a] = storage_map_a[var_a] + arg2;
        emit Event_ddf252ad(arg0, arg1, arg2);
    }
    
    /// @custom:selector    0x095ea7b3
    /// @custom:signature   Unresolved_095ea7b3(uint256 arg0, uint256 arg1) public payable
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_095ea7b3(uint256 arg0, uint256 arg1) public payable {
        require(!msg.data.length < 0x44);
        address var_a = msg.sender;
        var_a = arg0;
        storage_map_a[var_a] = arg1;
        emit Event_8c5be1e5(msg.sender, arg0, arg1);
    }
    
    /// @custom:selector    0x70a08231
    /// @custom:signature   Unresolved_70a08231(uint256 arg0) public view returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_70a08231(uint256 arg0) public view returns (uint256) {
        require(!msg.data.length < 0x24);
        uint256 var_a = arg0;
        return storage_map_a[var_a];
    }
}