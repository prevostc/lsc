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
    uint256 public unresolved_b187bd26;
    
    event Event_90890809();
    event Event_a45f47fd();
    event Event_9e87fac8();
    event Event_f279e6a1();
    error CustomError_00000000();
    
    /// @custom:selector    0x4cdad506
    /// @custom:signature   Unresolved_4cdad506(uint256 arg0) public returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_4cdad506(uint256 arg0) public returns (uint256) {
        require(!msg.data.length < 0x24);
        var_a = 0x70a0823100000000000000000000000000000000000000000000000000000000;
        address var_b = address(this);
        (bool success, bytes memory ret0) = address(store_a).{ gas: 0x0f4240 }Unresolved_70a08231(var_b); // staticcall
        require((!ret0.length < 0x20) & (ret0.length < 0x40));
        require(!(var_a + 0x01) < var_a);
        require(!(store_b + 0x0f4240) < store_b);
        require(store_b + 0x0f4240);
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        require((!var_a + 0x01) | (((var_a + 0x01) * arg0) / (var_a + 0x01) == arg0));
        uint256 var_a = ((var_a + 0x01) * arg0) / (store_b + 0x0f4240);
        return ((var_a + 0x01) * arg0) / (store_b + 0x0f4240);
    }
    
    /// @custom:selector    0x8456cb59
    /// @custom:signature   Unresolved_8456cb59() public
    function Unresolved_8456cb59() public {
        require(msg.sender == store_c, CustomError_30cd7471());
        unresolved_b187bd26 = 0x01;
        emit Event_9e87fac8();
    }
    
    /// @custom:selector    0x3f4ba83a
    /// @custom:signature   Unresolved_3f4ba83a() public
    function Unresolved_3f4ba83a() public {
        require(msg.sender == store_c, CustomError_30cd7471());
        unresolved_b187bd26 = 0;
        emit Event_a45f47fd();
    }
    
    /// @custom:selector    0xef8b30f7
    /// @custom:signature   Unresolved_ef8b30f7(uint256 arg0) public returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_ef8b30f7(uint256 arg0) public returns (uint256) {
        require(!msg.data.length < 0x24);
        address var_b = address(this);
        (bool success, bytes memory ret0) = address(store_a).{ gas: 0x0f4240 }Unresolved_70a08231(var_b); // staticcall
        require((!ret0.length < 0x20) & (ret0.length < 0x40));
        require(!(store_b + 0x0f4240) < store_b);
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        require(!(var_a + 0x01) < var_a);
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        require(var_a + 0x01);
        require((!store_b + 0x0f4240) | (((store_b + 0x0f4240) * arg0) / (store_b + 0x0f4240) == arg0));
        uint256 var_a = ((store_b + 0x0f4240) * arg0) / (var_a + 0x01);
        return ((store_b + 0x0f4240) * arg0) / (var_a + 0x01);
    }
    
    /// @custom:selector    0x2e1a7d4d
    /// @custom:signature   Unresolved_2e1a7d4d(uint256 arg0) public returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_2e1a7d4d(uint256 arg0) public returns (uint256) {
        require(!msg.data.length < 0x24);
        transient[0] = 0x01;
        require(unresolved_b187bd26 == 0, CustomError_9e87fac8());
        require(0 < arg0, CustomError_39996567());
        address var_b = msg.sender;
        require(!(storage_map_e[var_b] < arg0), CustomError_39996567());
        var_a = 0x70a0823100000000000000000000000000000000000000000000000000000000;
        address var_d = address(this);
        (bool success, bytes memory ret0) = address(store_a).{ gas: 0x0f4240 }Unresolved_70a08231(var_d); // staticcall
        require((!ret0.length < 0x20) & (ret0.length < 0x40));
        require(!(var_a + 0x01) < var_a);
        require(!(store_b + 0x0f4240) < store_b);
        require(store_b + 0x0f4240);
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        require((!var_a + 0x01) | (((var_a + 0x01) * arg0) / (var_a + 0x01) == arg0));
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        require(0 < (((var_a + 0x01) * arg0) / (store_b + 0x0f4240)));
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
        emit Event_f279e6a1(msg.sender, ((var_a + 0x01) * arg0) / (store_b + 0x0f4240), arg0);
        transient[0] = 0;
        var_a = ((var_a + 0x01) * arg0) / (store_b + 0x0f4240);
        return ((var_a + 0x01) * arg0) / (store_b + 0x0f4240);
    }
    
    /// @custom:selector    0xb6b55f25
    /// @custom:signature   Unresolved_b6b55f25(uint256 arg0) public returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_b6b55f25(uint256 arg0) public returns (uint256) {
        require(!msg.data.length < 0x24);
        transient[0] = 0x01;
        require(unresolved_b187bd26 == 0, CustomError_9e87fac8());
        require(0 < arg0);
        address var_b = address(this);
        (bool success, bytes memory ret0) = address(store_a).{ gas: 0x0f4240 }Unresolved_70a08231(var_b); // staticcall
        require((!ret0.length < 0x20) & (ret0.length < 0x40));
        require(!(store_b + 0x0f4240) < store_b);
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        require(!(var_a + 0x01) < var_a);
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        require(var_a + 0x01);
        require((!store_b + 0x0f4240) | (((store_b + 0x0f4240) * arg0) / (store_b + 0x0f4240) == arg0));
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        require(0 < (((store_b + 0x0f4240) * arg0) / (var_a + 0x01)));
        require(!(store_b + (((store_b + 0x0f4240) * arg0) / (var_a + 0x01))) < store_b);
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        store_b = store_b + (((store_b + 0x0f4240) * arg0) / (var_a + 0x01));
        address var_c = msg.sender;
        require(!(storage_map_f[var_c] + (((store_b + 0x0f4240) * arg0) / (var_a + 0x01))) < storage_map_f[var_c]);
        var_a = 0x4e487b7100000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        storage_map_f[var_c] = storage_map_f[var_c] + (((store_b + 0x0f4240) * arg0) / (var_a + 0x01));
        var_a = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_b = msg.sender;
        (bool success, bytes memory ret0) = address(store_a).{ gas: 0x0f4240 }Unresolved_23b872dd(var_b); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (ret0.length < 0x40)), CustomError_90b8ec18());
        require((!ret0.length | var_a) == 0x01, CustomError_90b8ec18());
        address var_a = msg.sender;
        emit Event_90890809(msg.sender, arg0, ((store_b + 0x0f4240) * arg0) / (var_a + 0x01));
        transient[0] = 0;
        var_a = ((store_b + 0x0f4240) * arg0) / (var_a + 0x01);
        return ((store_b + 0x0f4240) * arg0) / (var_a + 0x01);
    }
}