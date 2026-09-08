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
    mapping(bytes32 => bytes32) storage_map_a;
    bytes32 store_e;
    uint256 store_c;
    bytes public getReserves;
    uint256 store_f;
    bytes32 store_d;
    
    event RemoveLiquidity(address, uint256, uint256, uint256);
    event Event_ec43a82f();
    error Zero();
    event Event_268d208c();
    event AddLiquidity(address, uint256, uint256, uint256);
    
    /// @custom:selector    0xf5eb42dc
    /// @custom:signature   Unresolved_f5eb42dc(uint256 arg0) public view returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_f5eb42dc(uint256 arg0) public view returns (uint256) {
        require(!msg.data.length < 0x24);
        uint256 var_a = arg0;
        return storage_map_a[var_a];
    }
    
    /// @custom:selector    0x21d2da23
    /// @custom:signature   Unresolved_21d2da23(uint256 arg0, uint256 arg1) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_21d2da23(uint256 arg0, uint256 arg1) public payable returns (uint256) {
        require(!(msg.data.length < 0x44), CustomError_bb2875c3());
        require(0 < arg0, CustomError_bb2875c3());
        require(0 < getReserves, CustomError_bb2875c3());
        require(0 < store_c, CustomError_bb2875c3());
        require(!((store_c + arg0) < store_c), CustomError_bb2875c3());
        require(store_c + arg0, CustomError_bb2875c3());
        require(!arg0 | (((arg0 * getReserves) / arg0) == getReserves), CustomError_bb2875c3());
        require(!((arg0 * getReserves) / (store_c + arg0) < arg1), CustomError_bb2875c3());
        require(0 < ((arg0 * getReserves) / (store_c + arg0)));
        require(!(store_c + arg0) < store_c);
        store_c = store_c + arg0;
        require(!getReserves < ((arg0 * getReserves) / (store_c + arg0)));
        getReserves = getReserves - ((arg0 * getReserves) / (store_c + arg0));
        var_a = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        address var_b = msg.sender;
        (bool success, bytes memory ret0) = address(store_d).{ gas: 0x0f4240 }Unresolved_23b872dd(var_b); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_a == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_a = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_b = msg.sender;
        (bool success, bytes memory ret0) = address(store_e).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_b); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_a == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_ec43a82f(msg.sender, arg0, (arg0 * getReserves) / (store_c + arg0));
        return (arg0 * getReserves) / (store_c + arg0);
    }
    
    /// @custom:selector    0x2b1087f0
    /// @custom:signature   Unresolved_2b1087f0(uint256 arg0, uint256 arg1) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_2b1087f0(uint256 arg0, uint256 arg1) public payable returns (uint256) {
        require(!(msg.data.length < 0x44), CustomError_bb2875c3());
        require(0 < arg0, CustomError_bb2875c3());
        require(0 < getReserves, CustomError_bb2875c3());
        require(0 < store_c, CustomError_bb2875c3());
        require(!((getReserves + arg0) < getReserves), CustomError_bb2875c3());
        require(getReserves + arg0, CustomError_bb2875c3());
        require(!arg0 | (((arg0 * store_c) / arg0) == store_c), CustomError_bb2875c3());
        require(!((arg0 * store_c) / (getReserves + arg0) < arg1), CustomError_bb2875c3());
        require(0 < ((arg0 * store_c) / (getReserves + arg0)));
        require(!(getReserves + arg0) < getReserves);
        getReserves = getReserves + arg0;
        require(!store_c < ((arg0 * store_c) / (getReserves + arg0)));
        store_c = store_c - ((arg0 * store_c) / (getReserves + arg0));
        var_a = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        address var_b = msg.sender;
        (bool success, bytes memory ret0) = address(store_e).{ gas: 0x0f4240 }Unresolved_23b872dd(var_b); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_a == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_a = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_b = msg.sender;
        (bool success, bytes memory ret0) = address(store_d).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_b); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_a == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_268d208c(msg.sender, arg0, (arg0 * store_c) / (getReserves + arg0));
        return (arg0 * store_c) / (getReserves + arg0);
    }
    
    /// @custom:selector    0x9cd441da
    /// @custom:signature   addLiquidity(uint256 arg0, uint256 arg1) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function addLiquidity(uint256 arg0, uint256 arg1) public payable returns (uint256) {
        require(!msg.data.length < 0x44);
        uint256 var_a = arg0;
        uint256 var_b = arg1;
        require(0 < var_a);
        require(0 < var_b);
        require(0 == (store_f == 0));
        require(0 < getReserves);
        require(0 < store_c);
        require(getReserves);
        require(!var_a | (((var_a * store_f) / var_a) == store_f));
        require(store_c);
        require(!var_b | (((var_b * store_f) / var_b) == store_f));
        require(0 == (!((var_b * store_f) / store_c) < ((var_a * store_f) / getReserves)));
        require(0 < ((var_b * store_f) / store_c));
        require(!(getReserves + var_a) < getReserves);
        getReserves = getReserves + var_a;
        require(!(store_c + var_b) < store_c);
        store_c = store_c + var_b;
        require(!(((var_b * store_f) / store_c) + store_f) < ((var_b * store_f) / store_c));
        store_f = ((var_b * store_f) / store_c) + store_f;
        address var_e = msg.sender;
        require(!(((var_b * store_f) / store_c) + storage_map_g[var_e]) < ((var_b * store_f) / store_c));
        var_e = msg.sender;
        storage_map_g[var_e] = ((var_b * store_f) / store_c) + storage_map_g[var_e];
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        address var_d = msg.sender;
        (bool success, bytes memory ret0) = address(store_e).{ gas: 0x0f4240 }Unresolved_23b872dd(var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        (bool success, bytes memory ret0) = address(store_d).{ gas: 0x0f4240 }Unresolved_23b872dd(var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit AddLiquidity(msg.sender, var_a, var_b, (var_b * store_f) / store_c);
        return (var_b * store_f) / store_c;
        require(0 < ((var_a * store_f) / getReserves));
        require(!(getReserves + var_a) < getReserves);
        getReserves = getReserves + var_a;
        require(!(store_c + var_b) < store_c);
        store_c = store_c + var_b;
        require(!(((var_a * store_f) / getReserves) + store_f) < ((var_a * store_f) / getReserves));
        store_f = ((var_a * store_f) / getReserves) + store_f;
        var_e = msg.sender;
        require(!(((var_a * store_f) / getReserves) + storage_map_g[var_e]) < ((var_a * store_f) / getReserves));
        var_e = msg.sender;
        storage_map_g[var_e] = ((var_a * store_f) / getReserves) + storage_map_g[var_e];
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        var_g = address(this);
        var_h = var_a;
        (bool success, bytes memory ret0) = address(store_e).{ gas: 0x0f4240 }transferFrom(var_d, var_g, var_h); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        var_g = address(this);
        var_h = var_b;
        (bool success, bytes memory ret0) = address(store_d).{ gas: 0x0f4240 }transferFrom(var_d, var_g, var_h); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit AddLiquidity(msg.sender, var_a, var_b, (var_a * store_f) / getReserves);
        return (var_a * store_f) / getReserves;
        require(0 < var_a);
        require(!(getReserves + var_a) < getReserves);
        getReserves = getReserves + var_a;
        require(!(store_c + var_b) < store_c);
        store_c = store_c + var_b;
        require(!(var_a + store_f) < var_a);
        store_f = var_a + store_f;
        var_e = msg.sender;
        require(!(var_a + storage_map_g[var_e]) < var_a);
        var_e = msg.sender;
        storage_map_g[var_e] = var_a + storage_map_g[var_e];
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        var_g = address(this);
        var_h = var_a;
        (bool success, bytes memory ret0) = address(store_e).{ gas: 0x0f4240 }transferFrom(var_d, var_g, var_h); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        var_g = address(this);
        var_h = var_b;
        (bool success, bytes memory ret0) = address(store_d).{ gas: 0x0f4240 }transferFrom(var_d, var_g, var_h); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit AddLiquidity(msg.sender, var_a, var_b, var_a);
        return var_a;
    }
    
    /// @custom:selector    0x9c8f9f23
    /// @custom:signature   removeLiquidity(uint256 arg0) public payable returns (bytes memory)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function removeLiquidity(uint256 arg0) public payable returns (bytes memory) {
        require(!(msg.data.length < 0x24), CustomError_39996567());
        require(0 < arg0, CustomError_39996567());
        address var_a = msg.sender;
        require(!(storage_map_a[var_a] < arg0), CustomError_39996567());
        require(0 < store_f);
        require(store_f);
        require(!arg0 | (((arg0 * getReserves) / arg0) == getReserves));
        require(store_f);
        require(!arg0 | (((arg0 * store_c) / arg0) == store_c));
        require(0 < ((arg0 * getReserves) / store_f));
        require(0 < ((arg0 * store_c) / store_f));
        require(!storage_map_a[var_a] < arg0);
        var_a = msg.sender;
        storage_map_a[var_a] = storage_map_a[var_a] - arg0;
        require(!store_f < arg0);
        store_f = store_f - arg0;
        require(!getReserves < ((arg0 * getReserves) / store_f));
        getReserves = getReserves - ((arg0 * getReserves) / store_f);
        require(!store_c < ((arg0 * store_c) / store_f));
        store_c = store_c - ((arg0 * store_c) / store_f);
        var_c = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        address var_d = msg.sender;
        (bool success, bytes memory ret0) = address(store_e).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_c = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        (bool success, bytes memory ret0) = address(store_d).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit RemoveLiquidity(msg.sender, (arg0 * getReserves) / store_f, (arg0 * store_c) / store_f, arg0);
        return abi.encodePacked((arg0 * getReserves) / store_f, (arg0 * store_c) / store_f);
    }
    
    /// @custom:selector    0x19d4b175
    /// @custom:signature   Unresolved_19d4b175(uint256 arg0) public view returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_19d4b175(uint256 arg0) public view returns (uint256) {
        require(!(msg.data.length < 0x24), CustomError_f4560403());
        require(0 < arg0, CustomError_f4560403());
        require(0 < getReserves, CustomError_f4560403());
        require(!((getReserves + arg0) < getReserves), CustomError_f4560403());
        require(getReserves + arg0, CustomError_f4560403());
        require(!arg0 | (((arg0 * store_c) / arg0) == store_c), CustomError_f4560403());
        return (arg0 * store_c) / (getReserves + arg0);
    }
}