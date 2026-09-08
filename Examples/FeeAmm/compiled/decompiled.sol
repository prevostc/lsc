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
    bytes public collectProtocolFees;
    bytes public getReserves;
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
    event FeeToSet(address);
    event ProtocolFeesCollected(address, uint256, uint256);
    event RemoveLiquidity(address, uint256, uint256, uint256);
    error NotOwner();
    event AddLiquidity(address, uint256, uint256, uint256);
    
    /// @custom:selector    0x2b1087f0
    /// @custom:signature   Unresolved_2b1087f0(uint256 arg0, uint256 arg1) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_2b1087f0(uint256 arg0, uint256 arg1) public payable returns (uint256) {
        require(!(msg.data.length < 0x44), CustomError_bb2875c3());
        uint256 var_a = arg0;
        require(0 < var_a, CustomError_bb2875c3());
        require(0 < getReserves, CustomError_bb2875c3());
        require(0 < store_b, CustomError_bb2875c3());
        require(0x2710, CustomError_bb2875c3());
        require(!var_a | (((var_a * 0x26f2) / var_a) == 0x26f2), CustomError_bb2875c3());
        require(!((getReserves + ((var_a * 0x26f2) / 0x2710)) < getReserves), CustomError_bb2875c3());
        require(getReserves + ((var_a * 0x26f2) / 0x2710), CustomError_bb2875c3());
        require((!(var_a * 0x26f2) / 0x2710) | ((((var_a * 0x26f2) / 0x2710) * store_b) / ((var_a * 0x26f2) / 0x2710) == store_b), CustomError_bb2875c3());
        require(!((((var_a * 0x26f2) / 0x2710) * store_b) / (getReserves + ((var_a * 0x26f2) / 0x2710)) < arg1), CustomError_bb2875c3());
        require(0 < ((((var_a * 0x26f2) / 0x2710) * store_b) / (getReserves + ((var_a * 0x26f2) / 0x2710))));
        require(0 == (store_c == 0));
        require(0x2710);
        require(!var_a | (((var_a * 0x26f2) / var_a) == 0x26f2));
        require(!var_a < ((var_a * 0x26f2) / 0x2710));
        require(0x2710);
        require((!var_a - ((var_a * 0x26f2) / 0x2710)) | (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / (var_a - ((var_a * 0x26f2) / 0x2710)) == store_d));
        require(!var_a < (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710));
        require(!(getReserves + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710))) < getReserves);
        getReserves = getReserves + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710));
        require(!store_b < ((((var_a * 0x26f2) / 0x2710) * store_b) / (getReserves + ((var_a * 0x26f2) / 0x2710))));
        store_b = store_b - ((((var_a * 0x26f2) / 0x2710) * store_b) / (getReserves + ((var_a * 0x26f2) / 0x2710)));
        require(!(collectProtocolFees + (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710)) < collectProtocolFees);
        collectProtocolFees = collectProtocolFees + (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710);
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
        emit Event_268d208c(msg.sender, var_a, (((var_a * 0x26f2) / 0x2710) * store_b) / (getReserves + ((var_a * 0x26f2) / 0x2710)));
        return (((var_a * 0x26f2) / 0x2710) * store_b) / (getReserves + ((var_a * 0x26f2) / 0x2710));
        require(!(getReserves + var_a) < getReserves);
        getReserves = getReserves + var_a;
        require(!store_b < ((((var_a * 0x26f2) / 0x2710) * store_b) / (getReserves + ((var_a * 0x26f2) / 0x2710))));
        store_b = store_b - ((((var_a * 0x26f2) / 0x2710) * store_b) / (getReserves + ((var_a * 0x26f2) / 0x2710)));
        var_b = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }gasprice_bit_ether(var_c); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_b == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_b = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        var_d = (((var_a * 0x26f2) / 0x2710) * store_b) / (getReserves + ((var_a * 0x26f2) / 0x2710));
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }transfer(var_c, var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_b == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_268d208c(msg.sender, var_a, (((var_a * 0x26f2) / 0x2710) * store_b) / (getReserves + ((var_a * 0x26f2) / 0x2710)));
        return (((var_a * 0x26f2) / 0x2710) * store_b) / (getReserves + ((var_a * 0x26f2) / 0x2710));
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
        require(0 == (store_i == 0));
        require(0 < getReserves);
        require(0 < store_b);
        require(getReserves);
        require(!var_a | (((var_a * store_i) / var_a) == store_i));
        require(store_b);
        require(!var_b | (((var_b * store_i) / var_b) == store_i));
        require(0 == (!((var_b * store_i) / store_b) < ((var_a * store_i) / getReserves)));
        require(0 < ((var_b * store_i) / store_b));
        require(!(getReserves + var_a) < getReserves);
        getReserves = getReserves + var_a;
        require(!(store_b + var_b) < store_b);
        store_b = store_b + var_b;
        require(!(((var_b * store_i) / store_b) + store_i) < ((var_b * store_i) / store_b));
        store_i = ((var_b * store_i) / store_b) + store_i;
        address var_e = msg.sender;
        require(!(((var_b * store_i) / store_b) + storage_map_j[var_e]) < ((var_b * store_i) / store_b));
        var_e = msg.sender;
        storage_map_j[var_e] = ((var_b * store_i) / store_b) + storage_map_j[var_e];
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
        emit AddLiquidity(msg.sender, var_a, var_b, (var_b * store_i) / store_b);
        return (var_b * store_i) / store_b;
        require(0 < ((var_a * store_i) / getReserves));
        require(!(getReserves + var_a) < getReserves);
        getReserves = getReserves + var_a;
        require(!(store_b + var_b) < store_b);
        store_b = store_b + var_b;
        require(!(((var_a * store_i) / getReserves) + store_i) < ((var_a * store_i) / getReserves));
        store_i = ((var_a * store_i) / getReserves) + store_i;
        var_e = msg.sender;
        require(!(((var_a * store_i) / getReserves) + storage_map_j[var_e]) < ((var_a * store_i) / getReserves));
        var_e = msg.sender;
        storage_map_j[var_e] = ((var_a * store_i) / getReserves) + storage_map_j[var_e];
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        var_g = address(this);
        var_h = var_a;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }transferFrom(var_d, var_g, var_h); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        var_g = address(this);
        var_h = var_b;
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }transferFrom(var_d, var_g, var_h); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit AddLiquidity(msg.sender, var_a, var_b, (var_a * store_i) / getReserves);
        return (var_a * store_i) / getReserves;
        require(0 < var_a);
        require(!(getReserves + var_a) < getReserves);
        getReserves = getReserves + var_a;
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
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }transferFrom(var_d, var_g, var_h); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_c == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_c = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_d = msg.sender;
        var_g = address(this);
        var_h = var_b;
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }transferFrom(var_d, var_g, var_h); // call
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
        require(!(storage_map_k[var_a] < arg0), CustomError_39996567());
        require(0 < store_i);
        require(store_i);
        require(!arg0 | (((arg0 * getReserves) / arg0) == getReserves));
        require(store_i);
        require(!arg0 | (((arg0 * store_b) / arg0) == store_b));
        require(0 < ((arg0 * getReserves) / store_i));
        require(0 < ((arg0 * store_b) / store_i));
        require(!storage_map_k[var_a] < arg0);
        var_a = msg.sender;
        storage_map_k[var_a] = storage_map_k[var_a] - arg0;
        require(!store_i < arg0);
        store_i = store_i - arg0;
        require(!getReserves < ((arg0 * getReserves) / store_i));
        getReserves = getReserves - ((arg0 * getReserves) / store_i);
        require(!store_b < ((arg0 * store_b) / store_i));
        store_b = store_b - ((arg0 * store_b) / store_i);
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
        emit RemoveLiquidity(msg.sender, (arg0 * getReserves) / store_i, (arg0 * store_b) / store_i, arg0);
        return abi.encodePacked((arg0 * getReserves) / store_i, (arg0 * store_b) / store_i);
    }
    
    /// @custom:selector    0xf46901ed
    /// @custom:signature   Unresolved_f46901ed(uint256 arg0) public payable
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function Unresolved_f46901ed(uint256 arg0) public payable {
        require(!(msg.data.length < 0x24), CustomError_30cd7471());
        require(msg.sender == store_l, CustomError_30cd7471());
        store_c = arg0;
        emit FeeToSet(arg0);
    }
    
    /// @custom:selector    0x21d2da23
    /// @custom:signature   Unresolved_21d2da23(uint256 arg0, uint256 arg1) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_21d2da23(uint256 arg0, uint256 arg1) public payable returns (uint256) {
        require(!(msg.data.length < 0x44), CustomError_bb2875c3());
        uint256 var_a = arg0;
        require(0 < var_a, CustomError_bb2875c3());
        require(0 < getReserves, CustomError_bb2875c3());
        require(0 < store_b, CustomError_bb2875c3());
        require(0x2710, CustomError_bb2875c3());
        require(!var_a | (((var_a * 0x26f2) / var_a) == 0x26f2), CustomError_bb2875c3());
        require(!((store_b + ((var_a * 0x26f2) / 0x2710)) < store_b), CustomError_bb2875c3());
        require(store_b + ((var_a * 0x26f2) / 0x2710), CustomError_bb2875c3());
        require((!(var_a * 0x26f2) / 0x2710) | ((((var_a * 0x26f2) / 0x2710) * getReserves) / ((var_a * 0x26f2) / 0x2710) == getReserves), CustomError_bb2875c3());
        require(!((((var_a * 0x26f2) / 0x2710) * getReserves) / (store_b + ((var_a * 0x26f2) / 0x2710)) < arg1), CustomError_bb2875c3());
        require(0 < ((((var_a * 0x26f2) / 0x2710) * getReserves) / (store_b + ((var_a * 0x26f2) / 0x2710))));
        require(0 == (store_c == 0));
        require(0x2710);
        require(!var_a | (((var_a * 0x26f2) / var_a) == 0x26f2));
        require(!var_a < ((var_a * 0x26f2) / 0x2710));
        require(0x2710);
        require((!var_a - ((var_a * 0x26f2) / 0x2710)) | (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / (var_a - ((var_a * 0x26f2) / 0x2710)) == store_d));
        require(!var_a < (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710));
        require(!(store_b + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710))) < store_b);
        store_b = store_b + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710));
        require(!getReserves < ((((var_a * 0x26f2) / 0x2710) * getReserves) / (store_b + ((var_a * 0x26f2) / 0x2710))));
        getReserves = getReserves - ((((var_a * 0x26f2) / 0x2710) * getReserves) / (store_b + ((var_a * 0x26f2) / 0x2710)));
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
        emit Event_ec43a82f(msg.sender, var_a, (((var_a * 0x26f2) / 0x2710) * getReserves) / (store_b + ((var_a * 0x26f2) / 0x2710)));
        return (((var_a * 0x26f2) / 0x2710) * getReserves) / (store_b + ((var_a * 0x26f2) / 0x2710));
        require(!(store_b + var_a) < store_b);
        store_b = store_b + var_a;
        require(!getReserves < ((((var_a * 0x26f2) / 0x2710) * getReserves) / (store_b + ((var_a * 0x26f2) / 0x2710))));
        getReserves = getReserves - ((((var_a * 0x26f2) / 0x2710) * getReserves) / (store_b + ((var_a * 0x26f2) / 0x2710)));
        var_b = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }gasprice_bit_ether(var_c); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_b == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        var_b = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        var_d = (((var_a * 0x26f2) / 0x2710) * getReserves) / (store_b + ((var_a * 0x26f2) / 0x2710));
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }transfer(var_c, var_d); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (var_b == 0x01)), CustomError_90b8ec18());
        require(!(0x01 == 0), CustomError_90b8ec18());
        emit Event_ec43a82f(msg.sender, var_a, (((var_a * 0x26f2) / 0x2710) * getReserves) / (store_b + ((var_a * 0x26f2) / 0x2710)));
        return (((var_a * 0x26f2) / 0x2710) * getReserves) / (store_b + ((var_a * 0x26f2) / 0x2710));
    }
    
    /// @custom:selector    0xce9c0bb7
    /// @custom:signature   setProtocolShare(uint256 arg0) public payable
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    function setProtocolShare(uint256 arg0) public payable {
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