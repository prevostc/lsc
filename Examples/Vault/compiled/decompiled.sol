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
    mapping(bytes32 => bytes32) storage_map_g;
    mapping(bytes32 => bytes32) storage_map_e;
    uint256 store_a;
    bytes32 store_c;
    uint256 store_b;
    bytes32 store_f;
    uint256 public unresolved_67dda112;
    
    event Event_90890809();
    event Event_a45f47fd();
    event Event_9e87fac8();
    event Event_f279e6a1();
    error CustomError_00000000();
    
    /// @custom:selector    0x4cdad506
    /// @custom:signature   Unresolved_4cdad506(uint256 arg0) public view returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_4cdad506(uint256 arg0) public view returns (uint256) {
        require(!msg.data.length < 0x24);
        require(store_a);
        require(!store_b | (((store_b * arg0) / store_b) == arg0));
        return (store_b * arg0) / store_a;
    }
    
    /// @custom:selector    0x8456cb59
    /// @custom:signature   Unresolved_8456cb59() public payable
    function Unresolved_8456cb59() public payable {
        require(msg.sender == store_c, CustomError_30cd7471());
        unresolved_67dda112 = 0x01;
        emit Event_9e87fac8();
    }
    
    /// @custom:selector    0x3f4ba83a
    /// @custom:signature   Unresolved_3f4ba83a() public payable
    function Unresolved_3f4ba83a() public payable {
        require(msg.sender == store_c, CustomError_30cd7471());
        unresolved_67dda112 = 0;
        emit Event_a45f47fd();
    }
    
    /// @custom:selector    0xef8b30f7
    /// @custom:signature   Unresolved_ef8b30f7(uint256 arg0) public view returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_ef8b30f7(uint256 arg0) public view returns (uint256) {
        require(!msg.data.length < 0x24);
        require(0 == (store_a == 0));
        require(store_b);
        require(!store_a | (((store_a * arg0) / store_a) == arg0));
        return (store_a * arg0) / store_b;
        return arg0;
    }
    
    /// @custom:selector    0x2e1a7d4d
    /// @custom:signature   Unresolved_2e1a7d4d(uint256 arg0) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_2e1a7d4d(uint256 arg0) public payable returns (uint256) {
        require(!(msg.data.length < 0x24), CustomError_9e87fac8());
        require(unresolved_67dda112 == 0, CustomError_9e87fac8());
        require(0 < arg0, CustomError_39996567());
        address var_b = msg.sender;
        require(!(storage_map_e[var_b] < arg0), CustomError_39996567());
        require(store_a);
        require(!store_b | (((store_b * arg0) / store_b) == arg0));
        require(0 < ((store_b * arg0) / store_a));
        require(!storage_map_e[var_b] < arg0);
        var_b = msg.sender;
        storage_map_e[var_b] = storage_map_e[var_b] - arg0;
        require(!store_a < arg0);
        store_a = store_a - arg0;
        require(!store_b < ((store_b * arg0) / store_a));
        store_b = store_b - ((store_b * arg0) / store_a);
        var_a = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        address var_d = msg.sender;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_a == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_f279e6a1(msg.sender, (store_b * arg0) / store_a, arg0);
        return (store_b * arg0) / store_a;
    }
    
    /// @custom:selector    0xb6b55f25
    /// @custom:signature   Unresolved_b6b55f25(uint256 arg0) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_b6b55f25(uint256 arg0) public payable returns (uint256) {
        require(!(msg.data.length < 0x24), CustomError_9e87fac8());
        require(unresolved_67dda112 == 0, CustomError_9e87fac8());
        require(0 < arg0);
        require(0 == (store_a == 0));
        require(store_b);
        require(!store_a | (((store_a * arg0) / store_a) == arg0));
        require(0 < ((store_a * arg0) / store_b));
        var_a = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        address var_b = msg.sender;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_23b872dd(var_b); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_a == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        require(!(store_b + arg0) < store_b);
        store_b = store_b + arg0;
        require(!(((store_a * arg0) / store_b) + store_a) < ((store_a * arg0) / store_b));
        store_a = ((store_a * arg0) / store_b) + store_a;
        address var_e = msg.sender;
        require(!(((store_a * arg0) / store_b) + storage_map_g[var_e]) < ((store_a * arg0) / store_b));
        var_e = msg.sender;
        storage_map_g[var_e] = ((store_a * arg0) / store_b) + storage_map_g[var_e];
        uint256 var_g = arg0;
        emit Event_90890809(msg.sender, arg0, (store_a * arg0) / store_b);
        return (store_a * arg0) / store_b;
        require(0 < arg0);
        var_a = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_b = msg.sender;
        var_c = address(this);
        var_d = arg0;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_23b872dd(var_b, var_c, var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_a == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        require(!(store_b + arg0) < store_b);
        store_b = store_b + arg0;
        require(!(arg0 + store_a) < arg0);
        store_a = var_g + store_a;
        var_e = msg.sender;
        require(!(arg0 + storage_map_g[var_e]) < arg0);
        var_e = msg.sender;
        storage_map_g[var_e] = var_g + storage_map_g[var_e];
        emit Event_90890809(msg.sender, arg0, arg0);
        return arg0;
    }
}