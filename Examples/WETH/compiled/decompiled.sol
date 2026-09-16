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
    uint256 public totalSupply;
    mapping(bytes32 => bytes32) storage_map_a;
    
    event Withdrawal(address, uint256);
    event Approval(address, address, uint256);
    event Deposit(address, uint256);
    error InsufficientBalance();
    event Transfer(address, address, uint256);
    
    /// @custom:selector    0xa9059cbb
    /// @custom:signature   workMyDirefulOwner(uint256 arg0, uint256 arg1) public returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function workMyDirefulOwner(uint256 arg0, uint256 arg1) public returns (uint256) {
        require(!msg.data.length < 0x44);
        address var_a = msg.sender;
        require(!(storage_map_a[var_a] < arg1), CustomError_f4d678b8());
        require(!storage_map_a[var_a] < arg1);
        var_a = msg.sender;
        storage_map_a[var_a] = storage_map_a[var_a] - arg1;
        var_a = arg0;
        require(!(storage_map_a[var_a] + arg1) < storage_map_a[var_a]);
        var_a = arg0;
        storage_map_a[var_a] = storage_map_a[var_a] + arg1;
        emit Transfer(msg.sender, arg0, arg1);
        return 0x01;
    }
    
    /// @custom:selector    0x2e1a7d4d
    /// @custom:signature   withdraw(uint256 arg0) public
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function withdraw(uint256 arg0) public {
        require(!msg.data.length < 0x24);
        transient[0] = 0x01;
        address var_a = msg.sender;
        require(!(storage_map_a[var_a] < arg0), CustomError_90b8ec18());
        var_a = msg.sender;
        storage_map_a[var_a] = storage_map_a[var_a] - arg0;
        require(!(totalSupply < arg0), CustomError_90b8ec18());
        totalSupply = totalSupply - arg0;
        (bool success, bytes memory ret0) = address(msg.sender).transfer(arg0);
        require(success == 0x01, CustomError_90b8ec18());
        emit Withdrawal(msg.sender, arg0);
        transient[0] = 0;
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
    /// @custom:signature   Unresolved_23b872dd(uint256 arg0, uint256 arg1, uint256 arg2) public returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    /// @param              arg2 ["uint256", "bytes32", "int256"]
    function Unresolved_23b872dd(uint256 arg0, uint256 arg1, uint256 arg2) public returns (uint256) {
        require(!msg.data.length < 0x64);
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
        emit Transfer(arg0, arg1, arg2);
        return 0x01;
    }
    
    /// @custom:selector    0x095ea7b3
    /// @custom:signature   Unresolved_095ea7b3(uint256 arg0, uint256 arg1) public returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_095ea7b3(uint256 arg0, uint256 arg1) public returns (uint256) {
        require(!msg.data.length < 0x44);
        address var_a = msg.sender;
        var_a = arg0;
        storage_map_a[var_a] = arg1;
        emit Approval(msg.sender, arg0, arg1);
        return 0x01;
    }
    
    /// @custom:selector    0x70a08231
    /// @custom:signature   Unresolved_70a08231(uint256 arg0) public view returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_70a08231(uint256 arg0) public view returns (uint256) {
        require(!msg.data.length < 0x24);
        uint256 var_a = arg0;
        return storage_map_a[var_a];
    }
    
    /// @custom:selector    0xd0e30db0
    /// @custom:signature   deposit() public payable
    function deposit() public payable {
        address var_a = msg.sender;
        if (!(storage_map_a[var_a] + msg.value) < storage_map_a[var_a]) {
            var_a = msg.sender;
            storage_map_a[var_a] = storage_map_a[var_a] + msg.value;
            if (!(totalSupply + msg.value) < totalSupply) {
                totalSupply = totalSupply + msg.value;
                emit Deposit(msg.sender, msg.value);
            }
        }
    }
}