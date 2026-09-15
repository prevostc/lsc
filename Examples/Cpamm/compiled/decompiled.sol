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
    bytes public constant unresolved_1ad8b03b = ;
    bytes public constant unresolved_9cd441da = ;
    bytes public constant unresolved_9c8f9f23 = ;
    bytes public constant unresolved_f46901ed = ;
    bytes public constant unresolved_21d2da23 = ;
    bytes public constant unresolved_ce9c0bb7 = ;
    bytes public constant unresolved_0902f1ac = ;
    bytes public constant unresolved_f5eb42dc = ;
    
    bytes public unresolved_a1af5b9a;
    uint256 store_a;
    uint256 store_b;
    bytes32 store_c;
    bytes32 store_h;
    bytes32 store_g;
    bytes32 store_f;
    bytes32 store_d;
    
    event Event_d24ccccf();
    error CustomError_00000000();
    event Event_268d208c();
    
    /// @custom:selector    0x2b1087f0
    /// @custom:signature   Unresolved_2b1087f0(uint256 arg0, uint256 arg1) public payable returns (uint256)
    /// @param              arg0 ["uint256", "bytes32", "int256"]
    /// @param              arg1 ["uint256", "bytes32", "int256"]
    function Unresolved_2b1087f0(uint256 arg0, uint256 arg1) public payable returns (uint256) {
        require(!(msg.data.length < 0x44), CustomError_cd4e6167());
        transient[0] = 0x01;
        uint256 var_a = arg0;
        require(0 < var_a, CustomError_cd4e6167());
        require(0 < store_a, CustomError_cd4e6167());
        require(0 < store_b, CustomError_cd4e6167());
        require(0x2710, CustomError_cd4e6167());
        require(!var_a | (((var_a * 0x26f2) / var_a) == 0x26f2), CustomError_cd4e6167());
        require(!((store_a + ((var_a * 0x26f2) / 0x2710)) < store_a), CustomError_cd4e6167());
        require(store_a + ((var_a * 0x26f2) / 0x2710), CustomError_cd4e6167());
        require(!store_b | (((store_b * ((var_a * 0x26f2) / 0x2710)) / store_b) == ((var_a * 0x26f2) / 0x2710)), CustomError_cd4e6167());
        require(!(var_a < ((var_a * 0x26f2) / 0x2710)), CustomError_cd4e6167());
        require(0 == (store_c == 0), CustomError_cd4e6167());
        require(0x2710, CustomError_cd4e6167());
        require((!var_a - ((var_a * 0x26f2) / 0x2710)) | (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / (var_a - ((var_a * 0x26f2) / 0x2710)) == store_d), CustomError_cd4e6167());
        require(!((var_a - ((var_a * 0x26f2) / 0x2710)) < (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710)), CustomError_cd4e6167());
        require(!((store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710)) < arg1), CustomError_bb2875c3());
        require(0 < ((store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710))));
        require(!var_a < (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710));
        require(!(store_a + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710))) < store_a);
        store_a = store_a + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710));
        require(!store_b < ((store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710))));
        store_b = store_b - ((store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710)));
        require(!(unresolved_a1af5b9a + (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710)) < unresolved_a1af5b9a);
        unresolved_a1af5b9a = unresolved_a1af5b9a + (((var_a - ((var_a * 0x26f2) / 0x2710)) * store_d) / 0x2710);
        var_b = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        address var_c = msg.sender;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_23b872dd(var_c); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (ret0.length < 0x40)), CustomError_90b8ec18());
        require((!ret0.length | var_b) == 0x01, CustomError_90b8ec18());
        var_b = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_c); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (ret0.length < 0x40)), CustomError_90b8ec18());
        require((!ret0.length | var_b) == 0x01, CustomError_90b8ec18());
        emit Event_268d208c(msg.sender, var_a, (store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710)));
        transient[0] = 0;
        return (store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710));
        require(0x2710, CustomError_cd4e6167());
        require((!var_a - ((var_a * 0x26f2) / 0x2710)) | (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / (var_a - ((var_a * 0x26f2) / 0x2710)) == 0), CustomError_cd4e6167());
        require(!((var_a - ((var_a * 0x26f2) / 0x2710)) < (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710)), CustomError_cd4e6167());
        require(!((store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710)) < arg1), CustomError_bb2875c3());
        require(0 < ((store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710))));
        require(!var_a < (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710));
        require(!(store_a + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710))) < store_a);
        store_a = store_a + (var_a - (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710));
        require(!store_b < ((store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710))));
        store_b = store_b - ((store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710)));
        require(!(unresolved_a1af5b9a + (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710)) < unresolved_a1af5b9a);
        unresolved_a1af5b9a = unresolved_a1af5b9a + (((var_a - ((var_a * 0x26f2) / 0x2710)) * 0) / 0x2710);
        var_b = 0x23b872dd00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        var_d = address(this);
        var_e = var_a;
        (bool success, bytes memory ret0) = address(store_f).{ gas: 0x0f4240 }Unresolved_23b872dd(var_c, var_d, var_e); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (ret0.length < 0x40)), CustomError_90b8ec18());
        require((!ret0.length | var_b) == 0x01, CustomError_90b8ec18());
        var_b = 0xa9059cbb00000000000000000000000000000000000000000000000000000000;
        var_c = msg.sender;
        var_d = (store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710));
        (bool success, bytes memory ret0) = address(store_g).{ gas: 0x0f4240 }Unresolved_a9059cbb(var_c, var_d, var_e); // call
        require(!ret0.length | ((!ret0.length < 0x20) & (ret0.length < 0x40)), CustomError_90b8ec18());
        require((!ret0.length | var_b) == 0x01, CustomError_90b8ec18());
        emit Event_268d208c(msg.sender, var_a, (store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710)));
        transient[0] = 0;
        return (store_b * ((var_a * 0x26f2) / 0x2710)) / (store_a + ((var_a * 0x26f2) / 0x2710));
    }
}