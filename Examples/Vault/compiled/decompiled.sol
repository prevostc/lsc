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
    mapping(bytes32 => bytes32) storage_map_e;
    bytes32 store_a;
    bytes32 store_c;
    uint256 store_b;
    mapping(bytes32 => bytes32) storage_map_f;
    uint256 public isPaused;
    
    event Deposit(address, uint256, uint256);
    event Unpaused();
    event Paused();
    event Withdraw(address, uint256, uint256);
    error NotOwner();
    
    /// @custom:selector    0x4cdad506
    /// @custom:signature   previewRedeem(uint256 arg0) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function previewRedeem(uint256 arg0) public payable returns (uint256) {
        require(!msg.data.length < 0x24);
        var_a = 0x70a0823100000000000000000000000000000000000000000000000000000000;
        address var_b = address(this);
        (bool success, bytes memory ret0) = address(store_a).{ gas: 0x0f4240 }Unresolved_70a08231(var_b); // staticcall
        require((!ret0.length < 0x20) & (ret0.length < 0x40));
        require(store_b);
        require(!var_a | (((var_a * arg0) / var_a) == arg0));
        uint256 var_a = (var_a * arg0) / store_b;
        return (var_a * arg0) / store_b;
    }
    
    /// @custom:selector    0x8456cb59
    /// @custom:signature   pause() public payable
    function pause() public payable {
        require(msg.sender == store_c, CustomError_30cd7471());
        isPaused = 0x01;
        emit Paused();
    }
    
    /// @custom:selector    0x3f4ba83a
    /// @custom:signature   unpause() public payable
    function unpause() public payable {
        require(msg.sender == store_c, CustomError_30cd7471());
        isPaused = 0;
        emit Unpaused();
    }
    
    /// @custom:selector    0xef8b30f7
    /// @custom:signature   previewDeposit(uint256 arg0) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function previewDeposit(uint256 arg0) public payable returns (uint256) {
        require(!msg.data.length < 0x24);
        var_a = 0x70a0823100000000000000000000000000000000000000000000000000000000;
        address var_b = address(this);
        (bool success, bytes memory ret0) = address(store_a).{ gas: 0x0f4240 }Unresolved_70a08231(var_b); // staticcall
        require((!ret0.length < 0x20) & (ret0.length < 0x40));
        require(0 == (store_b == 0));
        require(var_a);
        require(!store_b | (((store_b * arg0) / store_b) == arg0));
        uint256 var_a = (store_b * arg0) / var_a;
        return (store_b * arg0) / var_a;
        require(0x01);
        require(!0x01 | (((0x01 * arg0) / 0x01) == arg0));
        return (0x01 * arg0) / 0x01;
    }
    
    /// @custom:selector    0x2e1a7d4d
    /// @custom:signature   withdraw(uint256 arg0) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function withdraw(uint256 arg0) public payable returns (uint256) {
        require(!(msg.data.length < 0x24), CustomError_9e87fac8());
        require(isPaused == 0, CustomError_9e87fac8());
        require(0 < arg0, CustomError_39996567());
        address var_b = msg.sender;
        require(!(storage_map_e[var_b] < arg0), CustomError_39996567());
        var_a = 0x70a0823100000000000000000000000000000000000000000000000000000000;
        address var_d = address(this);
        (bool success, bytes memory ret0) = address(store_a).{ gas: 0x0f4240 }Unresolved_70a08231(var_d); // staticcall
        require((!ret0.length < 0x20) & (ret0.length < 0x40));
        require(store_b);
        require(!var_a | (((var_a * arg0) / var_a) == arg0));
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        require(0 < ((var_a * arg0) / store_b));
        require(!storage_map_e[var_b] < arg0);
        var_b = msg.sender;
        storage_map_e[var_b] = storage_map_e[var_b] - arg0;
        require(!store_b < arg0);
        store_b = store_b - arg0;
        var_a = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        (bool success, bytes memory ret0) = address(store_a).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (ret0.length < 0x40)), CustomError_90b8ec18());
        require((!ret0.length | var_a) == 0x01, CustomError_90b8ec18());
        address var_a = msg.sender;
        emit Withdraw(msg.sender, (var_a * arg0) / store_b, arg0);
        var_a = (var_a * arg0) / store_b;
        return (var_a * arg0) / store_b;
    }
    
    /// @custom:selector    0xb6b55f25
    /// @custom:signature   deposit(uint256 arg0) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function deposit(uint256 arg0) public payable returns (uint256) {
        require(!(msg.data.length < 0x24), CustomError_9e87fac8());
        require(isPaused == 0, CustomError_9e87fac8());
        require(0 < arg0);
        var_a = 0x70a0823100000000000000000000000000000000000000000000000000000000;
        address var_b = address(this);
        (bool success, bytes memory ret0) = address(store_a).{ gas: 0x0f4240 }Unresolved_70a08231(var_b); // staticcall
        require((!ret0.length < 0x20) & (ret0.length < 0x40));
        require(0 == (store_b == 0));
        require(var_a);
        require(!store_b | (((store_b * arg0) / store_b) == arg0));
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        require(0 < ((store_b * arg0) / var_a));
        require(!(store_b + ((store_b * arg0) / var_a)) < store_b);
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        store_b = store_b + ((store_b * arg0) / var_a);
        address var_c = msg.sender;
        require(!(storage_map_f[var_c] + ((store_b * arg0) / var_a)) < storage_map_f[var_c]);
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        storage_map_f[var_c] = storage_map_f[var_c] + ((store_b * arg0) / var_a);
        var_a = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_b = msg.sender;
        (bool success, bytes memory ret0) = address(store_a).{ gas: 0x0f4240 }Unresolved_23b872dd(var_b); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (ret0.length < 0x40)), CustomError_90b8ec18());
        require((!ret0.length | var_a) == 0x01, CustomError_90b8ec18());
        address var_a = msg.sender;
        emit Deposit(msg.sender, arg0, (store_b * arg0) / var_a);
        var_a = (store_b * arg0) / var_a;
        return (store_b * arg0) / var_a;
        require(0x01);
        require(!0x01 | (((0x01 * arg0) / 0x01) == arg0));
        require(0 < ((0x01 * arg0) / 0x01));
        require(!(store_b + ((0x01 * arg0) / 0x01)) < store_b);
        store_b = store_b + ((0x01 * arg0) / 0x01);
        var_c = msg.sender;
        require(!(storage_map_f[var_c] + ((0x01 * arg0) / 0x01)) < storage_map_f[var_c]);
        var_c = msg.sender;
        storage_map_f[var_c] = storage_map_f[var_c] + ((0x01 * arg0) / 0x01);
        var_a = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_b = msg.sender;
        (bool success, bytes memory ret0) = address(store_a).{ gas: 0x0f4240 }gasprice_bit_ether(var_b); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (ret0.length < 0x40)), CustomError_90b8ec18());
        require((!ret0.length | var_a) == 0x01, CustomError_90b8ec18());
        emit Deposit(msg.sender, arg0, (0x01 * arg0) / 0x01);
        return (0x01 * arg0) / 0x01;
    }
}