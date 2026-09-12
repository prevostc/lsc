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
    bytes public unresolved_a1af5b9a;
    bytes public unresolved_0902f1ac;
    uint256 store_b;
    uint256 store_c;
    uint256 store_h;
    bytes32 store_g;
    bytes32 store_f;
    uint256 store_i;
    bytes32 store_l;
    mapping(bytes32 => bytes32) storage_map_j;
    mapping(bytes32 => bytes32) storage_map_k;
    uint256 store_d;
    
    event Event_ec43a82f();
    event Event_ac9f8df6();
    event Event_268d208c();
    event Event_e7ba424f();
    event Event_d24ccccf();
    event Event_59c3a0b6();
    error CustomError_00000000();
    event Event_beb38857();
    
    /// @custom:selector    0x2b1087f0
    /// @custom:signature   Unresolved_2b1087f0(uint256 arg0, uint256 arg1) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_2b1087f0(uint256 arg0, uint256 arg1) public payable returns (uint256) {
        require(!(msg.data.length < 0x44), CustomError_bb2875c3());
        uint256 var_a = arg0;
        require(0 < var_a, CustomError_bb2875c3());
        require(0 < unresolved_0902f1ac, CustomError_bb2875c3());
        require(0 < store_b, CustomError_bb2875c3());
        require(0x2710, CustomError_bb2875c3());
        require(!var_a | (((var_a * 0x26f2) / var_a) == 0x26f2), CustomError_bb2875c3());
        require(!((unresolved_0902f1ac + ((var_a * 0x26f2) / 0x2710)) < unresolved_0902f1ac), CustomError_bb2875c3());
        require(unresolved_0902f1ac + ((var_a * 0x26f2) / 0x2710), CustomError_bb2875c3());
        uint256 var_d = store_b * ((var_a * 0x26f2) / 0x2710);
        require(!store_b | ((var_d / store_b) == ((var_a * 0x26f2) / 0x2710)), CustomError_bb2875c3());
        var_d = var_d / (unresolved_0902f1ac + ((var_a * 0x26f2) / 0x2710));
        require(!(var_d < arg1), CustomError_bb2875c3());
        require(0 < var_d);
        require(0 == (store_c == 0));
        require(0x2710);
        require(!var_a | (((var_a * 0x26f2) / var_a) == 0x26f2));
        require(!var_a < ((var_a * 0x26f2) / 0x2710));
        require(0x2710);
        require((!var_a - ((var_a * 0x26f2) / 0x2710)) | (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / (var_a - ((var_a * 0x26f2) / 0x2710)) == store_d));
        require(!var_a < (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710));
        require(!(unresolved_0902f1ac + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710))) < unresolved_0902f1ac);
        unresolved_0902f1ac = unresolved_0902f1ac + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710));
        require(!store_b < var_d);
        store_b = store_b - var_d;
        require(!(unresolved_a1af5b9a + (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710)) < unresolved_a1af5b9a);
        unresolved_a1af5b9a = unresolved_a1af5b9a + (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710);
        var_b = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        address var_c = msg.sender;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_23b872dd(var_c); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_b == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_b = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_c); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_b == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_268d208c(msg.sender, var_a, var_d);
        return var_d;
        require(0x2710);
        require(!var_a | (((var_a * 0x26f2) / var_a) == 0x26f2));
        require(!var_a < ((var_a * 0x26f2) / 0x2710));
        require(0x2710);
        require((!var_a - ((var_a * 0x26f2) / 0x2710)) | (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / (var_a - ((var_a * 0x26f2) / 0x2710)) == 0));
        require(!var_a < (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710));
        require(!(unresolved_0902f1ac + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710))) < unresolved_0902f1ac);
        unresolved_0902f1ac = unresolved_0902f1ac + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710));
        require(!store_b < var_d);
        store_b = store_b - var_d;
        require(!(unresolved_a1af5b9a + (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710)) < unresolved_a1af5b9a);
        unresolved_a1af5b9a = unresolved_a1af5b9a + (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710);
        var_b = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        var_e = address(this);
        var_f = var_a;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_23b872dd(var_c, var_e, var_f); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_b == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_b = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        var_e = var_d;
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_c, var_e, var_f); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_b == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_268d208c(msg.sender, var_a, var_d);
        return var_d;
    }
    
    /// @custom:selector    0x9cd441da
    /// @custom:signature   Unresolved_9cd441da(uint256 arg0, uint256 arg1) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_9cd441da(uint256 arg0, uint256 arg1) public payable returns (uint256) {
        require(!msg.data.length < 0x44);
        uint256 var_a = arg0;
        uint256 var_b = arg1;
        require(0 < var_a);
        require(0 < var_b);
        require(0 == (store_i == 0));
        require(0 < unresolved_0902f1ac);
        require(0 < store_b);
        require(unresolved_0902f1ac);
        require(!store_i | (((store_i * var_a) / store_i) == var_a));
        require(store_b);
        require(!store_i | (((store_i * var_b) / store_i) == var_b));
        require(0 == (!((store_i * var_b) / store_b) < ((store_i * var_a) / unresolved_0902f1ac)));
        require(0 < ((store_i * var_b) / store_b));
        require(!(unresolved_0902f1ac + var_a) < unresolved_0902f1ac);
        unresolved_0902f1ac = unresolved_0902f1ac + var_a;
        require(!(store_b + var_b) < store_b);
        store_b = store_b + var_b;
        require(!(((store_i * var_b) / store_b) + store_i) < ((store_i * var_b) / store_b));
        store_i = ((store_i * var_b) / store_b) + store_i;
        address var_e = msg.sender;
        require(!(((store_i * var_b) / store_b) + storage_map_j[var_e]) < ((store_i * var_b) / store_b));
        var_e = msg.sender;
        storage_map_j[var_e] = ((store_i * var_b) / store_b) + storage_map_j[var_e];
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        address var_d = msg.sender;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_23b872dd(var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }Unresolved_23b872dd(var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_beb38857(msg.sender, var_a, var_b, (store_i * var_b) / store_b);
        return (store_i * var_b) / store_b;
        require(0 < ((store_i * var_a) / unresolved_0902f1ac));
        require(!(unresolved_0902f1ac + var_a) < unresolved_0902f1ac);
        unresolved_0902f1ac = unresolved_0902f1ac + var_a;
        require(!(store_b + var_b) < store_b);
        store_b = store_b + var_b;
        require(!(((store_i * var_a) / unresolved_0902f1ac) + store_i) < ((store_i * var_a) / unresolved_0902f1ac));
        store_i = ((store_i * var_a) / unresolved_0902f1ac) + store_i;
        var_e = msg.sender;
        require(!(((store_i * var_a) / unresolved_0902f1ac) + storage_map_j[var_e]) < ((store_i * var_a) / unresolved_0902f1ac));
        var_e = msg.sender;
        storage_map_j[var_e] = ((store_i * var_a) / unresolved_0902f1ac) + storage_map_j[var_e];
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        var_g = address(this);
        var_h = var_a;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_23b872dd(var_d, var_g, var_h, var_l); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        var_g = address(this);
        var_h = var_b;
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }Unresolved_23b872dd(var_d, var_g, var_h, var_l); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_beb38857(msg.sender, var_a, var_b, (store_i * var_a) / unresolved_0902f1ac);
        return (store_i * var_a) / unresolved_0902f1ac;
        require(0 < var_a);
        require(!(unresolved_0902f1ac + var_a) < unresolved_0902f1ac);
        unresolved_0902f1ac = unresolved_0902f1ac + var_a;
        require(!(store_b + var_b) < store_b);
        store_b = store_b + var_b;
        require(!(var_a + store_i) < var_a);
        store_i = var_a + store_i;
        var_e = msg.sender;
        require(!(var_a + storage_map_j[var_e]) < var_a);
        var_e = msg.sender;
        storage_map_j[var_e] = var_a + storage_map_j[var_e];
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        var_g = address(this);
        var_h = var_a;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_23b872dd(var_d, var_g, var_h, var_l); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        var_g = address(this);
        var_h = var_b;
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }Unresolved_23b872dd(var_d, var_g, var_h, var_l); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_beb38857(msg.sender, var_a, var_b, var_a);
        return var_a;
    }
    
    /// @custom:selector    0x9c8f9f23
    /// @custom:signature   Unresolved_9c8f9f23(uint256 arg0) public payable returns (bytes memory)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_9c8f9f23(uint256 arg0) public payable returns (bytes memory) {
        require(!(msg.data.length < 0x24), CustomError_39996567());
        require(0 < arg0, CustomError_39996567());
        address var_a = msg.sender;
        require(!(storage_map_k[var_a] < arg0), CustomError_39996567());
        require(0 < store_i);
        require(store_i);
        require(!unresolved_0902f1ac | (((unresolved_0902f1ac * arg0) / unresolved_0902f1ac) == arg0));
        require(store_i);
        require(!store_b | (((store_b * arg0) / store_b) == arg0));
        require(0 < ((unresolved_0902f1ac * arg0) / store_i));
        require(0 < ((store_b * arg0) / store_i));
        require(!storage_map_k[var_a] < arg0);
        var_a = msg.sender;
        storage_map_k[var_a] = storage_map_k[var_a] - arg0;
        require(!store_i < arg0);
        store_i = store_i - arg0;
        require(!unresolved_0902f1ac < ((unresolved_0902f1ac * arg0) / store_i));
        unresolved_0902f1ac = unresolved_0902f1ac - ((unresolved_0902f1ac * arg0) / store_i);
        require(!store_b < ((store_b * arg0) / store_i));
        store_b = store_b - ((store_b * arg0) / store_i);
        var_c = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        address var_d = msg.sender;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_c = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_59c3a0b6(msg.sender, (unresolved_0902f1ac * arg0) / store_i, (store_b * arg0) / store_i, arg0);
        return abi.encodePacked((unresolved_0902f1ac * arg0) / store_i, (store_b * arg0) / store_i);
    }
    
    /// @custom:selector    0xf46901ed
    /// @custom:signature   Unresolved_f46901ed(uint256 arg0) public payable
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_f46901ed(uint256 arg0) public payable {
        require(!(msg.data.length < 0x24), CustomError_30cd7471());
        require(msg.sender == store_l, CustomError_30cd7471());
        store_c = arg0;
        emit Event_e7ba424f(arg0);
    }
    
    /// @custom:selector    0x21d2da23
    /// @custom:signature   Unresolved_21d2da23(uint256 arg0, uint256 arg1) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_21d2da23(uint256 arg0, uint256 arg1) public payable returns (uint256) {
        require(!(msg.data.length < 0x44), CustomError_bb2875c3());
        uint256 var_a = arg0;
        require(0 < var_a, CustomError_bb2875c3());
        require(0 < unresolved_0902f1ac, CustomError_bb2875c3());
        require(0 < store_b, CustomError_bb2875c3());
        require(0x2710, CustomError_bb2875c3());
        require(!var_a | (((var_a * 0x26f2) / var_a) == 0x26f2), CustomError_bb2875c3());
        require(!((store_b + ((var_a * 0x26f2) / 0x2710)) < store_b), CustomError_bb2875c3());
        require(store_b + ((var_a * 0x26f2) / 0x2710), CustomError_bb2875c3());
        uint256 var_d = unresolved_0902f1ac * ((var_a * 0x26f2) / 0x2710);
        require(!unresolved_0902f1ac | ((var_d / unresolved_0902f1ac) == ((var_a * 0x26f2) / 0x2710)), CustomError_bb2875c3());
        var_d = var_d / (store_b + ((var_a * 0x26f2) / 0x2710));
        require(!(var_d < arg1), CustomError_bb2875c3());
        require(0 < var_d);
        require(0 == (store_c == 0));
        require(0x2710);
        require(!var_a | (((var_a * 0x26f2) / var_a) == 0x26f2));
        require(!var_a < ((var_a * 0x26f2) / 0x2710));
        require(0x2710);
        require((!var_a - ((var_a * 0x26f2) / 0x2710)) | (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / (var_a - ((var_a * 0x26f2) / 0x2710)) == store_d));
        require(!var_a < (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710));
        require(!(store_b + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710))) < store_b);
        store_b = store_b + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710));
        require(!unresolved_0902f1ac < var_d);
        unresolved_0902f1ac = unresolved_0902f1ac - var_d;
        require(!(store_h + (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710)) < store_h);
        store_h = store_h + (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710);
        var_b = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        address var_c = msg.sender;
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }Unresolved_23b872dd(var_c); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_b == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_b = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_c); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_b == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_ec43a82f(msg.sender, var_a, var_d);
        return var_d;
        require(0x2710);
        require(!var_a | (((var_a * 0x26f2) / var_a) == 0x26f2));
        require(!var_a < ((var_a * 0x26f2) / 0x2710));
        require(0x2710);
        require((!var_a - ((var_a * 0x26f2) / 0x2710)) | (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / (var_a - ((var_a * 0x26f2) / 0x2710)) == 0));
        require(!var_a < (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710));
        require(!(store_b + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710))) < store_b);
        store_b = store_b + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710));
        require(!unresolved_0902f1ac < var_d);
        unresolved_0902f1ac = unresolved_0902f1ac - var_d;
        require(!(store_h + (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710)) < store_h);
        store_h = store_h + (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710);
        var_b = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        var_e = address(this);
        var_f = var_a;
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }Unresolved_23b872dd(var_c, var_e, var_f); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_b == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_b = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        var_e = var_d;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_c, var_e, var_f); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_b == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_ec43a82f(msg.sender, var_a, var_d);
        return var_d;
    }
    
    /// @custom:selector    0xce9c0bb7
    /// @custom:signature   Unresolved_ce9c0bb7(uint256 arg0) public payable
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_ce9c0bb7(uint256 arg0) public payable {
        require(!(msg.data.length < 0x24), CustomError_30cd7471());
        require(msg.sender == store_l, CustomError_30cd7471());
        require(!(0x2710 < arg0), CustomError_cd4e6167());
        store_d = arg0;
        emit Event_ac9f8df6(arg0);
    }
    
    /// @custom:selector    0xf5eb42dc
    /// @custom:signature   Unresolved_f5eb42dc(uint256 arg0) public view returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_f5eb42dc(uint256 arg0) public view returns (uint256) {
        require(!msg.data.length < 0x24);
        uint256 var_a = arg0;
        return storage_map_k[var_a];
    }
}